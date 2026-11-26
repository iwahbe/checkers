//! Stack overflow (§13.3): a call that goes past the end of its stack
//! touches the protected region below it, and the fault ends the program
//! with `checkers runtime: stack overflow` and exit code 70, as running out
//! of memory does.
//!
//! The handler runs on an alternate signal stack (the overflowed one has no
//! room), set up for each thread that runs compiled code (`thread_init`).
//! It tells an overflow from any other fault by the address: one inside a
//! registered guard region (a fiber stack's, or a thread's own). Any other
//! fault goes to the handler that was there before, or kills the process as
//! it would have. The handler does nothing but async-signal-safe work:
//! atomic loads and stores, `write` and `_exit`. So buffered standard output
//! is not written out first: output still in the buffer is lost.
//!
//! Compile-time evaluation (§14) runs on fibers it can abandon
//! (`fiber::recoverable`), and its code reads the stack `PROBE` bytes below
//! where each function's frame starts. Reaching the guard region that way
//! happens only in compiled Checkers code, which holds no lock, so the
//! handler can abandon the fiber safely: it continues the thread that ran
//! it, which reports the overflow to the compiler. An overflow anywhere
//! else (in the runtime's own code) can't be abandoned safely and ends the
//! process as at run time.

use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize, Ordering};

/// How far below its stack pointer compile-time code reads on entry to
/// each function (`ckc`'s code generator emits the read): room for the
/// runtime calls it makes, so its stack runs out in its own code.
pub const PROBE: usize = 1 << 20;

/// The message, as `fatal` writes it.
const MESSAGE: &[u8] = b"checkers runtime: stack overflow\n";

/// A guard region: addresses `[lo, hi)` that only a stack overflow touches.
/// Registered for good, in a list the handler reads without locking; a
/// thread's is released when the thread ends and reused by the next one.
pub struct Guard {
    lo: AtomicUsize,
    hi: AtomicUsize,
    /// The fiber to abandon when compile-time code overflows into this
    /// region (`fiber::recoverable`); null elsewhere.
    recover: AtomicPtr<crate::fiber::Fiber>,
    taken: AtomicBool,
    next: *const Guard,
}

// Written only through atomics; `next` never changes once listed.
unsafe impl Sync for Guard {}

static GUARDS: AtomicPtr<Guard> = AtomicPtr::new(std::ptr::null_mut());

impl Guard {
    /// Register `[lo, hi)` as a guard region.
    pub fn new(lo: usize, hi: usize) -> &'static Guard {
        let mut g = GUARDS.load(Ordering::Acquire) as *const Guard;
        while let Some(r) = unsafe { g.as_ref() } {
            if r.taken.compare_exchange(false, true, Ordering::AcqRel, Ordering::Relaxed).is_ok() {
                r.set(lo, hi);
                return r;
            }
            g = r.next;
        }
        let r: &'static mut Guard = Box::leak(Box::new(Guard {
            lo: AtomicUsize::new(lo),
            hi: AtomicUsize::new(hi),
            recover: AtomicPtr::new(std::ptr::null_mut()),
            taken: AtomicBool::new(true),
            next: std::ptr::null(),
        }));
        let mut head = GUARDS.load(Ordering::Acquire);
        loop {
            r.next = head;
            match GUARDS.compare_exchange(head, r, Ordering::AcqRel, Ordering::Acquire) {
                Ok(_) => return r,
                Err(h) => head = h,
            }
        }
    }

    fn set(&self, lo: usize, hi: usize) {
        self.hi.store(0, Ordering::Release);
        self.lo.store(lo, Ordering::Release);
        self.hi.store(hi, Ordering::Release);
    }

    /// No longer a guard region (its thread has ended).
    fn release(&self) {
        self.set(0, 0);
        self.taken.store(false, Ordering::Release);
    }

    /// Abandon `f` when compiled code overflows into this region; null to stop.
    pub(crate) fn recover_to(&self, f: *mut crate::fiber::Fiber) {
        self.recover.store(f, Ordering::Release);
    }
}

/// The guard region `addr` is in.
fn find(addr: usize) -> Option<&'static Guard> {
    let mut g = GUARDS.load(Ordering::Acquire) as *const Guard;
    while let Some(r) = unsafe { g.as_ref() } {
        if r.lo.load(Ordering::Acquire) <= addr && addr < r.hi.load(Ordering::Acquire) {
            return Some(r);
        }
        g = r.next;
    }
    None
}

/// The handlers there were before ours, for faults that aren't overflows.
struct Previous(std::cell::UnsafeCell<[std::mem::MaybeUninit<libc::sigaction>; 2]>);
// Written once, before our handler is installed; only read after.
unsafe impl Sync for Previous {}
static PREVIOUS: Previous = Previous(std::cell::UnsafeCell::new([std::mem::MaybeUninit::uninit(); 2]));
const SIGNALS: [libc::c_int; 2] = [libc::SIGSEGV, libc::SIGBUS];

fn install() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| unsafe {
        let prev = &mut *PREVIOUS.0.get();
        for (i, sig) in SIGNALS.iter().enumerate() {
            libc::sigaction(*sig, std::ptr::null(), prev[i].as_mut_ptr());
        }
        for sig in SIGNALS {
            let mut a: libc::sigaction = std::mem::zeroed();
            a.sa_sigaction = on_fault as *const () as usize;
            a.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;
            libc::sigemptyset(&mut a.sa_mask);
            libc::sigaction(sig, &a, std::ptr::null_mut());
        }
    });
}

unsafe extern "C" fn on_fault(sig: libc::c_int, info: *mut libc::siginfo_t, ctx: *mut libc::c_void) {
    unsafe {
        let addr = (*info).si_addr() as usize;
        if let Some(g) = find(addr) {
            let f = g.recover.load(Ordering::Acquire);
            // Only compile-time code's probe reads exactly `PROBE` below the
            // stack pointer: nothing else may touch the stack that far below.
            if !f.is_null() && addr == stack_pointer(ctx).wrapping_sub(PROBE) {
                let (sp, pc) = crate::fiber::abandon(f);
                continue_at(ctx, sp, pc);
                return;
            }
            libc::write(2, MESSAGE.as_ptr().cast(), MESSAGE.len());
            libc::_exit(70);
        }
        // Not an overflow: what would have happened without us.
        let i = if sig == libc::SIGSEGV { 0 } else { 1 };
        let prev = (*PREVIOUS.0.get())[i].assume_init_ref();
        let h = prev.sa_sigaction;
        if h == libc::SIG_DFL || h == libc::SIG_IGN {
            // Returning runs the faulting instruction again, which now
            // ends the process with the signal.
            let mut a: libc::sigaction = std::mem::zeroed();
            a.sa_sigaction = libc::SIG_DFL;
            libc::sigaction(sig, &a, std::ptr::null_mut());
        } else if prev.sa_flags & libc::SA_SIGINFO != 0 {
            let h: extern "C" fn(libc::c_int, *mut libc::siginfo_t, *mut libc::c_void) = std::mem::transmute(h);
            h(sig, info, ctx);
        } else {
            let h: extern "C" fn(libc::c_int) = std::mem::transmute(h);
            h(sig);
        }
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
unsafe fn stack_pointer(ctx: *mut libc::c_void) -> usize {
    unsafe { (*(ctx as *mut libc::ucontext_t)).uc_mcontext.gregs[libc::REG_RSP as usize] as usize }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
unsafe fn continue_at(ctx: *mut libc::c_void, sp: usize, pc: usize) {
    unsafe {
        let g = &mut (*(ctx as *mut libc::ucontext_t)).uc_mcontext.gregs;
        g[libc::REG_RSP as usize] = sp as i64;
        g[libc::REG_RIP as usize] = pc as i64;
    }
}

#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
unsafe fn stack_pointer(ctx: *mut libc::c_void) -> usize {
    unsafe { (*(ctx as *mut libc::ucontext_t)).uc_mcontext.sp as usize }
}

#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
unsafe fn continue_at(ctx: *mut libc::c_void, sp: usize, pc: usize) {
    unsafe {
        let m = &mut (*(ctx as *mut libc::ucontext_t)).uc_mcontext;
        m.sp = sp as u64;
        m.pc = pc as u64;
    }
}

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
unsafe fn stack_pointer(ctx: *mut libc::c_void) -> usize {
    unsafe { (*(*(ctx as *mut libc::ucontext_t)).uc_mcontext).__ss.__sp as usize }
}

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
unsafe fn continue_at(ctx: *mut libc::c_void, sp: usize, pc: usize) {
    unsafe {
        let s = &mut (*(*(ctx as *mut libc::ucontext_t)).uc_mcontext).__ss;
        s.__sp = sp as u64;
        s.__pc = pc as u64;
    }
}

/// What `thread_init` set up for this thread, undone when it ends.
struct ThreadState {
    /// Our alternate signal stack's mapping, if we made it.
    alt: Option<(usize, usize)>,
    guard: Option<&'static Guard>,
}

impl Drop for ThreadState {
    fn drop(&mut self) {
        if let Some(g) = self.guard {
            g.release();
        }
        if let Some((p, len)) = self.alt {
            unsafe {
                let mut off: libc::stack_t = std::mem::zeroed();
                off.ss_flags = libc::SS_DISABLE;
                libc::sigaltstack(&off, std::ptr::null_mut());
                libc::munmap(p as *mut libc::c_void, len);
            }
        }
    }
}

thread_local! {
    static STATE: std::cell::RefCell<Option<ThreadState>> = const { std::cell::RefCell::new(None) };
}

fn page_size() -> usize {
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
}

/// Make a stack overflow on this thread end the program with a message
/// (or come back to compile-time evaluation): install the handler once
/// for the process, give this thread an alternate signal stack if it has
/// none, and register its own stack's guard. Call at the start of every
/// thread that runs compiled code.
pub fn thread_init() {
    install();
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        if s.is_some() {
            return;
        }
        let page = page_size();
        let alt = unsafe {
            let mut cur: libc::stack_t = std::mem::zeroed();
            libc::sigaltstack(std::ptr::null(), &mut cur);
            if cur.ss_flags & libc::SS_DISABLE == 0 {
                None
            } else {
                // The handler's own frame is small; a page below is a guard.
                let len = page + (64 << 10).max(libc::SIGSTKSZ);
                let p = libc::mmap(std::ptr::null_mut(), len, libc::PROT_READ | libc::PROT_WRITE, libc::MAP_PRIVATE | libc::MAP_ANON, -1, 0);
                if p == libc::MAP_FAILED {
                    crate::prog::fatal("out of memory");
                }
                libc::mprotect(p, page, libc::PROT_NONE);
                let st = libc::stack_t { ss_sp: (p as usize + page) as *mut libc::c_void, ss_flags: 0, ss_size: len - page };
                libc::sigaltstack(&st, std::ptr::null_mut());
                Some((p as usize, len))
            }
        };
        let guard = thread_guard(page).map(|(lo, hi)| Guard::new(lo, hi));
        *s = Some(ThreadState { alt, guard });
    });
}

/// The guard region below this thread's own stack.
#[cfg(target_os = "linux")]
fn thread_guard(page: usize) -> Option<(usize, usize)> {
    unsafe {
        let mut attr: libc::pthread_attr_t = std::mem::zeroed();
        if libc::pthread_getattr_np(libc::pthread_self(), &mut attr) != 0 {
            return None;
        }
        let (mut addr, mut size, mut guard) = (std::ptr::null_mut(), 0, 0);
        let ok = libc::pthread_attr_getstack(&attr, &mut addr, &mut size) == 0 && libc::pthread_attr_getguardsize(&attr, &mut guard) == 0;
        libc::pthread_attr_destroy(&mut attr);
        if !ok {
            return None;
        }
        // glibc has reported the guard both inside and below the stack it
        // gives (`man pthread_attr_getguardsize`, BUGS): either side.
        let g = guard.max(page);
        let lo = addr as usize;
        Some((lo.saturating_sub(g), lo + g))
    }
}

/// The guard region below this thread's own stack.
#[cfg(target_vendor = "apple")]
fn thread_guard(page: usize) -> Option<(usize, usize)> {
    unsafe {
        let me = libc::pthread_self();
        let top = libc::pthread_get_stackaddr_np(me) as usize;
        let lo = top - libc::pthread_get_stacksize_np(me);
        Some((lo - page, lo))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::process::ExitStatusExt;

    /// Read the stack `PROBE` bytes below the stack pointer, as compiled
    /// compile-time code does on entry, then recurse.
    #[inline(never)]
    #[allow(unconditional_recursion)]
    fn probe_down(n: usize) -> usize {
        let v: usize;
        unsafe {
            #[cfg(target_arch = "x86_64")]
            std::arch::asm!("mov {t}, rsp", "sub {t}, {p}", "mov {t}, [{t}]", t = out(reg) v, p = in(reg) PROBE);
            #[cfg(target_arch = "aarch64")]
            std::arch::asm!("mov {t}, sp", "sub {t}, {t}, {p}", "ldr {t}, [{t}]", t = out(reg) v, p = in(reg) PROBE);
        }
        let frame = [n; 16];
        std::hint::black_box(&frame);
        probe_down(n + 1) + v + frame[3]
    }

    #[inline(never)]
    #[allow(unconditional_recursion)]
    fn plain_down(n: usize) -> usize {
        let frame = [n; 16];
        std::hint::black_box(&frame);
        plain_down(n + 1) + frame[3]
    }

    #[test]
    fn probed_overflow_comes_back() {
        thread_init();
        // Twice: the stack is reused after its pages were given back.
        for _ in 0..2 {
            assert!(crate::fiber::recoverable(16 << 20, || probe_down(0)).is_none());
        }
        assert_eq!(crate::fiber::recoverable(16 << 20, || 7), Some(7));
    }

    /// Run this test binary's test `name` in a child with `CK_OVERFLOW_CHILD` set.
    fn child(name: &str) -> std::process::Output {
        std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", name, "--nocapture", "--test-threads", "1"])
            .env("CK_OVERFLOW_CHILD", "1")
            .output()
            .unwrap()
    }

    fn in_child() -> bool {
        std::env::var_os("CK_OVERFLOW_CHILD").is_some()
    }

    #[test]
    fn overflow_ends_the_program() {
        if in_child() {
            thread_init();
            crate::fiber::recoverable(16 << 20, || plain_down(0));
            return;
        }
        let o = child("overflow::tests::overflow_ends_the_program");
        assert_eq!(o.status.code(), Some(70));
        assert!(String::from_utf8_lossy(&o.stderr).contains("checkers runtime: stack overflow\n"));
    }

    #[test]
    fn overflow_of_a_thread_ends_the_program() {
        if in_child() {
            std::thread::Builder::new()
                .stack_size(1 << 20)
                .spawn(|| {
                    thread_init();
                    plain_down(0)
                })
                .unwrap()
                .join()
                .unwrap();
            return;
        }
        let o = child("overflow::tests::overflow_of_a_thread_ends_the_program");
        assert_eq!(o.status.code(), Some(70));
        assert!(String::from_utf8_lossy(&o.stderr).contains("checkers runtime: stack overflow\n"));
    }

    #[test]
    fn other_faults_still_crash() {
        if in_child() {
            thread_init();
            unsafe {
                std::ptr::read_volatile(std::hint::black_box(16usize) as *const usize);
            }
            return;
        }
        let o = child("overflow::tests::other_faults_still_crash");
        assert!(matches!(o.status.signal(), Some(libc::SIGSEGV) | Some(libc::SIGBUS)), "{:?}", o.status);
        assert!(!String::from_utf8_lossy(&o.stderr).contains("stack overflow"));
    }
}
