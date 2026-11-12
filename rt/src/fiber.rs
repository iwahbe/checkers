//! Fibers (M16, D113, §13.8): each behaviour runs on a stack of its own, so
//! a behaviour that would wait can be suspended in the middle of a call and
//! its thread can run others. x86-64 and ARM64; Linux and macOS (D116, D126).
//!
//! A stack is reserved address space (256 MiB, the depth D75 allows a
//! worker), committed by the kernel only as pages are touched, with a guard
//! page below. Stacks are reused through a pool. Switching saves the
//! callee-saved registers and the floating-point control state (on x86-64
//! the System V ABI's, with the SSE and x87 control words; on ARM64 the
//! AAPCS64's, x19–x30 and d8–d15, with FPCR), then swaps stack pointers.
//!
//! Thread-local state must not be read on both sides of a switch within one
//! function: a fiber may resume on another thread. The functions here that
//! touch thread-locals are `#[inline(never)]` and don't switch.

use std::cell::Cell;
use std::sync::Mutex;

/// Address space reserved for each fiber's stack.
pub const STACK: usize = 256 << 20;
const GUARD: usize = 4096;

/// Free stacks, for reuse: their lowest addresses.
static FREE: Mutex<Vec<usize>> = Mutex::new(Vec::new());

/// A reserved stack: `base` is its lowest address (the guard page).
struct Stack {
    base: usize,
}

impl Stack {
    fn get() -> Stack {
        if let Some(base) = FREE.lock().unwrap_or_else(|e| e.into_inner()).pop() {
            return Stack { base };
        }
        #[cfg(target_os = "linux")]
        let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE | libc::MAP_STACK;
        #[cfg(not(target_os = "linux"))]
        let flags = libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_NORESERVE;
        unsafe {
            let p = libc::mmap(std::ptr::null_mut(), STACK, libc::PROT_READ | libc::PROT_WRITE, flags, -1, 0);
            if p == libc::MAP_FAILED {
                crate::prog::fatal("could not reserve a stack for a behaviour");
            }
            if libc::mprotect(p, GUARD, libc::PROT_NONE) != 0 {
                crate::prog::fatal("could not protect a behaviour's stack");
            }
            Stack { base: p as usize }
        }
    }

    fn top(&self) -> usize {
        self.base + STACK
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        FREE.lock().unwrap_or_else(|e| e.into_inner()).push(self.base);
    }
}

/// How a fiber left the thread that ran it.
pub enum Left {
    /// Its body returned.
    Done,
    /// It is waiting: `register` is to be called, on the thread it left, once
    /// it has fully switched out, with what will resume it.
    Parked(Box<dyn FnOnce(Waker) + Send>),
}

/// What resumes a parked fiber: calling it hands the fiber back to its
/// scheduler. Called exactly once.
pub type Waker = Box<dyn FnOnce() + Send>;

/// A fiber's body: a function and its argument.
type Body = (fn(*mut ()), *mut ());

pub struct Fiber {
    stack: Stack,
    /// The fiber's saved stack pointer while it isn't running.
    sp: usize,
    /// The resuming thread's saved stack pointer while the fiber runs.
    back: usize,
    /// What to run next.
    body: Option<Body>,
    left: Option<Left>,
}

// A fiber runs on one thread at a time; its body's words are owned by it.
unsafe impl Send for Fiber {}

thread_local! {
    /// The fiber running on this thread, if any.
    static CURRENT: Cell<*mut Fiber> = const { Cell::new(std::ptr::null_mut()) };
    /// Finished fibers, ready for another body. Boxed: a fiber's stack holds
    /// its address, so a fiber never moves.
    #[allow(clippy::vec_box)]
    static IDLE: std::cell::RefCell<Vec<Box<Fiber>>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Idle fibers each thread keeps.
const KEEP: usize = 64;

#[inline(never)]
fn take_idle() -> Option<Box<Fiber>> {
    IDLE.with(|v| v.borrow_mut().pop())
}

#[inline(never)]
fn put_idle(f: Box<Fiber>) {
    IDLE.with(|v| {
        let mut v = v.borrow_mut();
        if v.len() < KEEP {
            v.push(f);
        }
    });
}

#[inline(never)]
fn current() -> *mut Fiber {
    CURRENT.with(|c| c.get())
}

#[inline(never)]
fn set_current(f: *mut Fiber) {
    CURRENT.with(|c| c.set(f));
}

/// Is this code running on a fiber (so that it may park)?
pub fn on_fiber() -> bool {
    !current().is_null()
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
std::arch::global_asm!(
    ".text",
    ".global ck_fiber_switch",
    ".type ck_fiber_switch,@function",
    // ck_fiber_switch(save: *mut usize, to: usize): save this context's stack
    // pointer at `save`, continue the one whose stack pointer is `to`.
    "ck_fiber_switch:",
    "push rbp",
    "push rbx",
    "push r12",
    "push r13",
    "push r14",
    "push r15",
    "sub rsp, 16",
    "stmxcsr [rsp]",
    "fnstcw [rsp + 4]",
    "mov [rdi], rsp",
    "mov rsp, rsi",
    "ldmxcsr [rsp]",
    "fldcw [rsp + 4]",
    "add rsp, 16",
    "pop r15",
    "pop r14",
    "pop r13",
    "pop r12",
    "pop rbx",
    "pop rbp",
    "ret",
    ".size ck_fiber_switch, .-ck_fiber_switch",
    ".global ck_fiber_start",
    ".type ck_fiber_start,@function",
    // A new fiber's first switch returns here, with its `Fiber` in r12.
    "ck_fiber_start:",
    "mov rdi, r12",
    "and rsp, -16",
    "call ck_fiber_main",
    "ud2",
    ".size ck_fiber_start, .-ck_fiber_start",
);

// ARM64 (AAPCS64; Apple's variant leaves x18 alone, as this does). A frame
// is 176 bytes: x19–x28, x29 (frame pointer), x30 (return address), d8–d15,
// FPCR, padding. Mach-O symbols carry a leading underscore.
#[cfg(target_arch = "aarch64")]
macro_rules! fiber_asm {
    ($switch:literal, $start:literal, $main:literal) => {
        std::arch::global_asm!(
            ".text",
            ".p2align 2",
            concat!(".global ", $switch),
            // switch(save: *mut usize, to: usize): save this context's stack
            // pointer at `save`, continue the one whose stack pointer is `to`.
            concat!($switch, ":"),
            "sub sp, sp, #176",
            "stp x19, x20, [sp, #0]",
            "stp x21, x22, [sp, #16]",
            "stp x23, x24, [sp, #32]",
            "stp x25, x26, [sp, #48]",
            "stp x27, x28, [sp, #64]",
            "stp x29, x30, [sp, #80]",
            "stp d8, d9, [sp, #96]",
            "stp d10, d11, [sp, #112]",
            "stp d12, d13, [sp, #128]",
            "stp d14, d15, [sp, #144]",
            "mrs x9, fpcr",
            "str x9, [sp, #160]",
            "mov x9, sp",
            "str x9, [x0]",
            "mov sp, x1",
            "ldr x9, [sp, #160]",
            "msr fpcr, x9",
            "ldp d14, d15, [sp, #144]",
            "ldp d12, d13, [sp, #128]",
            "ldp d10, d11, [sp, #112]",
            "ldp d8, d9, [sp, #96]",
            "ldp x29, x30, [sp, #80]",
            "ldp x27, x28, [sp, #64]",
            "ldp x25, x26, [sp, #48]",
            "ldp x23, x24, [sp, #32]",
            "ldp x21, x22, [sp, #16]",
            "ldp x19, x20, [sp, #0]",
            "add sp, sp, #176",
            "ret",
            concat!(".global ", $start),
            // A new fiber's first switch returns here, with its `Fiber` in x19.
            concat!($start, ":"),
            "mov x0, x19",
            concat!("bl ", $main),
            "brk #1",
        );
    };
}
#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
fiber_asm!("_ck_fiber_switch", "_ck_fiber_start", "_ck_fiber_main");
#[cfg(all(target_arch = "aarch64", not(target_vendor = "apple")))]
fiber_asm!("ck_fiber_switch", "ck_fiber_start", "ck_fiber_main");
#[cfg(not(any(all(target_arch = "x86_64", target_os = "linux"), target_arch = "aarch64")))]
compile_error!("fibers are implemented for Linux on x86-64 and for ARM64 (D126)");

extern "C" {
    fn ck_fiber_switch(save: *mut usize, to: usize);
    fn ck_fiber_start();
}

/// The bottom of every fiber: run each body it is given, leaving after each.
#[no_mangle]
extern "C" fn ck_fiber_main(f: *mut Fiber) -> ! {
    unsafe {
        loop {
            if let Some((run, arg)) = (*f).body.take() {
                if std::panic::catch_unwind(move || run(arg)).is_err() {
                    crate::prog::fatal("a behaviour panicked");
                }
            }
            (*f).left = Some(Left::Done);
            ck_fiber_switch(&mut (*f).sp, (*f).back);
        }
    }
}

impl Fiber {
    /// A fiber that runs `run(arg)` when next resumed: an idle one of this
    /// thread's, or a new one.
    pub fn with(run: fn(*mut ()), arg: *mut ()) -> Box<Fiber> {
        let mut f = take_idle().unwrap_or_else(Fiber::new);
        f.body = Some((run, arg));
        f
    }

    /// Keep a finished fiber for reuse on this thread.
    pub fn retire(f: Box<Fiber>) {
        put_idle(f);
    }

    fn new() -> Box<Fiber> {
        let stack = Stack::get();
        let mut f = Box::new(Fiber { stack, sp: 0, back: 0, body: None, left: None });
        let me = &mut *f as *mut Fiber as usize;
        let start = ck_fiber_start as *const () as usize;
        let top = f.stack.top() - 64;
        // The first switch to it pops this frame, then returns to the start
        // with the fiber in a callee-saved register.
        #[cfg(target_arch = "x86_64")]
        let frame: [usize; 10] = {
            // 16 bytes of control words, r15, r14, r13, r12 (the fiber), rbx, rbp, return address.
            let mut cw = 0u64;
            unsafe {
                std::arch::asm!("stmxcsr [{0}]", "fnstcw [{0} + 4]", in(reg) &mut cw as *mut u64, options(nostack));
            }
            [cw as usize, 0, 0, 0, 0, me, 0, 0, start, 0]
        };
        #[cfg(target_arch = "aarch64")]
        let frame: [usize; 22] = {
            // x19 (the fiber) … x28, x29, x30 (the start), d8 … d15, FPCR, padding.
            let fpcr: usize;
            unsafe {
                std::arch::asm!("mrs {0}, fpcr", out(reg) fpcr, options(nomem, nostack));
            }
            let mut fr = [0usize; 22];
            fr[0] = me;
            fr[11] = start;
            fr[20] = fpcr;
            fr
        };
        let sp = top - frame.len() * 8;
        unsafe {
            std::ptr::copy_nonoverlapping(frame.as_ptr(), sp as *mut usize, frame.len());
        }
        f.sp = sp;
        f
    }

    /// Run the fiber on this thread until it finishes or parks.
    pub fn resume(&mut self) -> Left {
        let prev = current();
        set_current(self);
        unsafe {
            ck_fiber_switch(&mut self.back, self.sp);
        }
        set_current(prev);
        self.left.take().unwrap_or(Left::Done)
    }
}

/// Park the running fiber: `register` gets what resumes it, after the fiber
/// has left its thread. Returns once it has been resumed (maybe on another
/// thread). Only call on a fiber.
#[inline(never)]
pub fn park(register: Box<dyn FnOnce(Waker) + Send>) {
    let f = current();
    if f.is_null() {
        crate::prog::bug("park outside a behaviour");
    }
    unsafe {
        (*f).left = Some(Left::Parked(register));
        ck_fiber_switch(&mut (*f).sp, (*f).back);
    }
}

/// Run `job` without holding this thread (D113): on a fiber, the fiber parks
/// and `job` runs on the blocking pool; elsewhere it just runs.
pub fn blocking<R: Send + 'static>(job: impl FnOnce() -> R + Send + 'static) -> R {
    if !on_fiber() {
        return job();
    }
    let slot: std::sync::Arc<Mutex<Option<R>>> = std::sync::Arc::new(Mutex::new(None));
    let out = slot.clone();
    park(Box::new(move |wake: Waker| {
        crate::blocking::submit(Box::new(move || {
            let r = job();
            *out.lock().unwrap_or_else(|e| e.into_inner()) = Some(r);
            wake();
        }));
    }));
    let r = slot.lock().unwrap_or_else(|e| e.into_inner()).take();
    r.unwrap_or_else(|| crate::prog::bug("a blocking job resumed without a result"))
}

/// A lock that parks a fiber that has to wait for it, rather than blocking
/// its thread, so it can be held while parked (standard input, D113).
pub struct FiberLock {
    busy: std::sync::atomic::AtomicBool,
    waiting: Mutex<std::collections::VecDeque<Waker>>,
}

impl FiberLock {
    pub const fn new() -> FiberLock {
        FiberLock { busy: std::sync::atomic::AtomicBool::new(false), waiting: Mutex::new(std::collections::VecDeque::new()) }
    }

    fn try_take(&self) -> bool {
        use std::sync::atomic::Ordering;
        self.busy.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok()
    }

    pub fn lock(&'static self) {
        loop {
            if self.try_take() {
                return;
            }
            if on_fiber() {
                park(Box::new(move |wake: Waker| {
                    let mut w = self.waiting.lock().unwrap_or_else(|e| e.into_inner());
                    // Released between the failed attempt and now: go on at once.
                    if !self.busy.load(std::sync::atomic::Ordering::Acquire) {
                        drop(w);
                        wake();
                    } else {
                        w.push_back(wake);
                    }
                }));
            } else {
                std::thread::yield_now();
            }
        }
    }

    pub fn unlock(&self) {
        let mut w = self.waiting.lock().unwrap_or_else(|e| e.into_inner());
        self.busy.store(false, std::sync::atomic::Ordering::Release);
        if let Some(wake) = w.pop_front() {
            drop(w);
            wake();
        }
    }
}

impl Default for FiberLock {
    fn default() -> Self {
        FiberLock::new()
    }
}

/// A reader whose system calls don't hold the thread: on a fiber, each read
/// runs on the blocking pool while the fiber is parked (D113). Put a buffer
/// above it, so that happens once per buffer, not once per line.
pub struct BlockingRead<R>(pub R);

/// The same for writing.
pub struct BlockingWrite<W>(pub W);

struct Raw<T>(*mut T, *mut u8, usize);
unsafe impl<T> Send for Raw<T> {}

impl<R: std::io::Read + Send + 'static> std::io::Read for BlockingRead<R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        if !on_fiber() {
            return self.0.read(buf);
        }
        // The fiber is parked until the job is done, so neither the reader
        // nor the buffer is touched by anyone else meanwhile.
        let raw = Raw(&mut self.0 as *mut R, buf.as_mut_ptr(), buf.len());
        blocking(move || {
            let raw = raw;
            unsafe { (*raw.0).read(std::slice::from_raw_parts_mut(raw.1, raw.2)) }
        })
    }
}

impl<W: std::io::Write + Send + 'static> std::io::Write for BlockingWrite<W> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        if !on_fiber() {
            return self.0.write(buf);
        }
        let raw = Raw(&mut self.0 as *mut W, buf.as_ptr() as *mut u8, buf.len());
        blocking(move || {
            let raw = raw;
            unsafe { (*raw.0).write(std::slice::from_raw_parts(raw.1, raw.2)) }
        })
    }

    fn flush(&mut self) -> std::io::Result<()> {
        if !on_fiber() {
            return self.0.flush();
        }
        let raw = Raw(&mut self.0 as *mut W, std::ptr::null_mut(), 0);
        blocking(move || {
            let raw = raw;
            unsafe { (*raw.0).flush() }
        })
    }
}
