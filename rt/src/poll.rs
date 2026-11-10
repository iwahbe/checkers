//! Waiting for pipes without holding a thread (M16, D113, §13.8): our ends of
//! a child's pipes are non-blocking; a read or write that would block parks
//! the behaviour and registers the descriptor with one `epoll` thread, which
//! wakes it when the descriptor is ready. Off a fiber (in `main`), the
//! thread waits in `poll` instead.

use crate::fiber::{self, Waker};
use std::collections::HashMap;
use std::io::{Read, Write};
use std::os::fd::{AsRawFd, OwnedFd, RawFd};
use std::sync::{Mutex, OnceLock};

/// The last token given out, and each registered wait: token → (descriptor, waker).
type Waits = (u64, HashMap<u64, (RawFd, Waker)>);

struct Poller {
    epfd: RawFd,
    waits: Mutex<Waits>,
}

static POLLER: OnceLock<Poller> = OnceLock::new();

fn poller() -> &'static Poller {
    POLLER.get_or_init(|| {
        let epfd = unsafe { libc::epoll_create1(libc::EPOLL_CLOEXEC) };
        if epfd < 0 {
            crate::prog::fatal("could not create the I/O poller");
        }
        std::thread::Builder::new()
            .name("checkers-poller".into())
            .stack_size(1 << 20)
            .spawn(serve)
            .unwrap_or_else(|_| crate::prog::fatal("could not start the I/O poller"));
        Poller { epfd, waits: Mutex::new((0, HashMap::new())) }
    })
}

fn serve() {
    let p = poller();
    let mut events: Vec<libc::epoll_event> = vec![libc::epoll_event { events: 0, u64: 0 }; 64];
    loop {
        let n = unsafe { libc::epoll_wait(p.epfd, events.as_mut_ptr(), events.len() as i32, -1) };
        if n < 0 {
            if std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            crate::prog::fatal("the I/O poller failed");
        }
        for e in &events[..n as usize] {
            let token = e.u64;
            let w = p.waits.lock().unwrap_or_else(|e| e.into_inner()).1.remove(&token);
            if let Some((fd, wake)) = w {
                unsafe { libc::epoll_ctl(p.epfd, libc::EPOLL_CTL_DEL, fd, std::ptr::null_mut()) };
                wake();
            }
        }
    }
}

/// Wait until `fd` can be read (or written): parked on a fiber, else in `poll`.
fn wait(fd: RawFd, write: bool) {
    let ev = if write { libc::EPOLLOUT } else { libc::EPOLLIN };
    if !fiber::on_fiber() {
        let mut pfd = libc::pollfd { fd, events: if write { libc::POLLOUT } else { libc::POLLIN }, revents: 0 };
        unsafe { libc::poll(&mut pfd, 1, -1) };
        return;
    }
    fiber::park(Box::new(move |wake: Waker| {
        let p = poller();
        let token = {
            let mut w = p.waits.lock().unwrap_or_else(|e| e.into_inner());
            w.0 += 1;
            let t = w.0;
            w.1.insert(t, (fd, wake));
            t
        };
        let mut e = libc::epoll_event { events: (ev | libc::EPOLLONESHOT | libc::EPOLLRDHUP) as u32, u64: token };
        if unsafe { libc::epoll_ctl(p.epfd, libc::EPOLL_CTL_ADD, fd, &mut e) } != 0 {
            // Can't be polled after all: let the caller retry, which blocks or fails.
            let w = p.waits.lock().unwrap_or_else(|e| e.into_inner()).1.remove(&token);
            if let Some((_, wake)) = w {
                wake();
            }
        }
    }));
}

/// One end of a pipe, non-blocking.
pub struct PollFd(OwnedFd);

impl PollFd {
    pub fn new(fd: OwnedFd) -> PollFd {
        unsafe {
            let raw = fd.as_raw_fd();
            let flags = libc::fcntl(raw, libc::F_GETFL);
            libc::fcntl(raw, libc::F_SETFL, flags | libc::O_NONBLOCK);
        }
        PollFd(fd)
    }
}

fn would_block(e: &std::io::Error) -> bool {
    e.kind() == std::io::ErrorKind::WouldBlock
}

impl Read for PollFd {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        loop {
            let n = unsafe { libc::read(self.0.as_raw_fd(), buf.as_mut_ptr() as *mut libc::c_void, buf.len()) };
            if n >= 0 {
                return Ok(n as usize);
            }
            let e = std::io::Error::last_os_error();
            if would_block(&e) {
                wait(self.0.as_raw_fd(), false);
            } else if e.kind() != std::io::ErrorKind::Interrupted {
                return Err(e);
            }
        }
    }
}

impl Write for PollFd {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        loop {
            let n = unsafe { libc::write(self.0.as_raw_fd(), buf.as_ptr() as *const libc::c_void, buf.len()) };
            if n >= 0 {
                return Ok(n as usize);
            }
            let e = std::io::Error::last_os_error();
            if would_block(&e) {
                wait(self.0.as_raw_fd(), true);
            } else if e.kind() != std::io::ErrorKind::Interrupted {
                return Err(e);
            }
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
