//! Waiting for pipes without holding a thread (M16, D113, §13.8): our ends of
//! a child's pipes are non-blocking; a read or write that would block parks
//! the behaviour and registers the descriptor with one poller thread
//! (`epoll` on Linux, `kqueue` on macOS, D126), which wakes it when the
//! descriptor is ready. Off a fiber, the thread waits in `poll` instead.

use crate::fiber::{self, Waker};
use std::collections::HashMap;
use std::io::{Read, Write};
use std::os::fd::{AsRawFd, OwnedFd, RawFd};
use std::sync::{Mutex, OnceLock};

/// The last token given out, and each registered wait: token → (descriptor, waker).
type Waits = (u64, HashMap<u64, (RawFd, Waker)>);

struct Poller {
    /// The `epoll` or `kqueue` descriptor.
    epfd: RawFd,
    waits: Mutex<Waits>,
}

/// The system's poller: create one, add a one-shot wait, wait for events.
#[cfg(target_os = "linux")]
mod sys {
    use std::os::fd::RawFd;

    pub fn create() -> RawFd {
        unsafe { libc::epoll_create1(libc::EPOLL_CLOEXEC) }
    }

    /// Wake `token` once `fd` is readable (or writable); false if it can't be polled.
    pub fn add(ep: RawFd, fd: RawFd, write: bool, token: u64) -> bool {
        let ev = if write { libc::EPOLLOUT } else { libc::EPOLLIN };
        let mut e = libc::epoll_event { events: (ev | libc::EPOLLONESHOT | libc::EPOLLRDHUP) as u32, u64: token };
        unsafe { libc::epoll_ctl(ep, libc::EPOLL_CTL_ADD, fd, &mut e) == 0 }
    }

    /// A one-shot wait that fired, removed so the descriptor can be added again.
    pub fn remove(ep: RawFd, fd: RawFd) {
        unsafe { libc::epoll_ctl(ep, libc::EPOLL_CTL_DEL, fd, std::ptr::null_mut()) };
    }

    /// Wait for events: their tokens, or `None` on an error other than an interruption.
    pub fn wait(ep: RawFd, out: &mut Vec<u64>) -> Option<()> {
        let mut events = [libc::epoll_event { events: 0, u64: 0 }; 64];
        let n = unsafe { libc::epoll_wait(ep, events.as_mut_ptr(), events.len() as i32, -1) };
        if n < 0 {
            return (std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted).then_some(());
        }
        out.extend(events[..n as usize].iter().map(|e| e.u64));
        Some(())
    }
}

#[cfg(target_vendor = "apple")]
mod sys {
    use std::os::fd::RawFd;

    pub fn create() -> RawFd {
        let kq = unsafe { libc::kqueue() };
        if kq >= 0 {
            unsafe { libc::fcntl(kq, libc::F_SETFD, libc::FD_CLOEXEC) };
        }
        kq
    }

    fn change(fd: RawFd, write: bool, flags: u16, token: u64) -> libc::kevent {
        libc::kevent {
            ident: fd as libc::uintptr_t,
            filter: if write { libc::EVFILT_WRITE } else { libc::EVFILT_READ },
            flags,
            fflags: 0,
            data: 0,
            udata: token as *mut libc::c_void,
        }
    }

    /// Wake `token` once `fd` is readable (or writable); false if it can't be polled.
    pub fn add(kq: RawFd, fd: RawFd, write: bool, token: u64) -> bool {
        let ch = change(fd, write, libc::EV_ADD | libc::EV_ONESHOT, token);
        unsafe { libc::kevent(kq, &ch, 1, std::ptr::null_mut(), 0, std::ptr::null()) == 0 }
    }

    /// A one-shot `kqueue` event removes itself.
    pub fn remove(_kq: RawFd, _fd: RawFd) {}

    /// Wait for events: their tokens, or `None` on an error other than an interruption.
    pub fn wait(kq: RawFd, out: &mut Vec<u64>) -> Option<()> {
        let mut events: [libc::kevent; 64] = unsafe { std::mem::zeroed() };
        let n = unsafe { libc::kevent(kq, std::ptr::null(), 0, events.as_mut_ptr(), events.len() as i32, std::ptr::null()) };
        if n < 0 {
            return (std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted).then_some(());
        }
        out.extend(events[..n as usize].iter().map(|e| e.udata as u64));
        Some(())
    }
}

static POLLER: OnceLock<Poller> = OnceLock::new();

fn poller() -> &'static Poller {
    POLLER.get_or_init(|| {
        let epfd = sys::create();
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
    let mut tokens = Vec::new();
    loop {
        tokens.clear();
        if sys::wait(p.epfd, &mut tokens).is_none() {
            crate::prog::fatal("the I/O poller failed");
        }
        for token in &tokens {
            let w = p.waits.lock().unwrap_or_else(|e| e.into_inner()).1.remove(token);
            if let Some((fd, wake)) = w {
                sys::remove(p.epfd, fd);
                wake();
            }
        }
    }
}

/// Wait until `fd` can be read (or written): parked on a fiber, else in `poll`.
fn wait(fd: RawFd, write: bool) {
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
        if !sys::add(p.epfd, fd, write, token) {
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
