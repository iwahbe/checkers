//! The lock-free behaviour scheduler (D66, D77), shared by the interpreter
//! and native code.
//!
//! Verona's algorithm (Cheeseman et al., OOPSLA 2023): every resource (a
//! cown, or a future) has a queue of requests, represented by its last
//! request alone. Scheduling a behaviour swaps itself in as the last
//! request of each of its resources, in address order. Where there was a
//! predecessor, it waits until the predecessor's behaviour has finished this
//! step on all of its resources (`scheduled`), then links itself behind it.
//! That makes scheduling on several resources appear atomic, which gives
//! causal order and rules out deadlock. A behaviour runs once every
//! predecessor has finished; on finishing it hands each resource to its
//! successor, or empties the queue.
//!
//! Runnable behaviours go to one ready queue served by the pool's threads,
//! except that a worker whose behaviour makes another runnable runs that
//! one next itself (in a fork/join tree, the last fork readies its join).
//! An idle worker spins a little before it sleeps, and only sleeping
//! workers are woken.

use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};

/// A resource: the last request in its queue, or null.
pub struct Resource {
    pub last: AtomicPtr<Request>,
}

impl Default for Resource {
    fn default() -> Self {
        Resource { last: AtomicPtr::new(std::ptr::null_mut()) }
    }
}

pub struct Request {
    /// The behaviour after this one on the same resource.
    next: AtomicPtr<Head>,
    /// This request's behaviour has finished scheduling on all its resources.
    scheduled: AtomicBool,
    res: *const Resource,
}

/// The part of a behaviour the queues see.
#[repr(C)]
struct Head {
    /// Predecessors still to finish, plus one while scheduling.
    count: AtomicUsize,
    reqs: Vec<Request>,
}

#[repr(C)]
struct Beh<P> {
    head: Head,
    payload: Option<P>,
}

struct Ptr<P>(*mut Beh<P>);
unsafe impl<P> Send for Ptr<P> {}

/// A thread's state, made once per worker, and how it runs a behaviour.
/// The payload stays with the scheduler until the behaviour has released
/// its resources: it is what keeps them alive.
pub trait Worker<P>: Send + 'static {
    type Error: Send + 'static;
    fn run(&mut self, p: &mut P) -> Result<(), Self::Error>;
}

pub struct Pool<P, E> {
    /// Runnable behaviours: lock-free, with a locked overflow when full.
    fast: Mpmc<Ptr<P>>,
    ready: Mutex<VecDeque<Ptr<P>>>,
    cv: Condvar,
    /// Scheduled and not yet finished.
    outstanding: AtomicUsize,
    /// Workers asleep on `cv`.
    idle: AtomicUsize,
    /// Behaviours in `ready` (read without the lock while spinning).
    queued: AtomicUsize,
    stop: AtomicBool,
    error: Mutex<Option<E>>,
    workers: Mutex<Vec<std::thread::JoinHandle<()>>>,
    /// Threads `par` may still start (D69).
    pub par_budget: AtomicUsize,
}

unsafe impl<P: Send, E: Send> Sync for Pool<P, E> {}
unsafe impl<P: Send, E: Send> Send for Pool<P, E> {}

/// Stack for each worker: behaviours may recurse deeply (a long list).
pub const WORKER_STACK: usize = 256 << 20;

fn spin(k: &mut u32) {
    *k += 1;
    if *k < 64 {
        std::hint::spin_loop();
    } else {
        std::thread::yield_now();
    }
}

impl<P: Send + 'static, E: Send + 'static> Pool<P, E> {
    /// A pool of `threads` threads: `threads - 1` workers now, and the
    /// calling thread once it calls `finish`.
    pub fn start<S: Worker<P, Error = E>>(threads: usize, make: impl Fn() -> S + Send + Sync + 'static) -> Arc<Self> {
        let pool = Arc::new(Pool {
            fast: Mpmc::new(1 << 16),
            ready: Mutex::new(VecDeque::new()),
            cv: Condvar::new(),
            outstanding: AtomicUsize::new(0),
            idle: AtomicUsize::new(0),
            queued: AtomicUsize::new(0),
            stop: AtomicBool::new(false),
            error: Mutex::new(None),
            workers: Mutex::new(Vec::new()),
            par_budget: AtomicUsize::new(threads.saturating_sub(1)),
        });
        let make = Arc::new(make);
        for _ in 1..threads.max(2) {
            let (p, make) = (pool.clone(), make.clone());
            let h = std::thread::Builder::new()
                .stack_size(WORKER_STACK)
                .spawn(move || {
                    let mut s = make();
                    p.work(&mut s, false);
                })
                .expect("spawn a worker thread");
            pool.workers.lock().unwrap().push(h);
        }
        pool
    }

    /// Schedule `payload` on `resources` (D66).
    pub fn submit(&self, resources: &[&Resource], payload: P) {
        let mut rs: Vec<*const Resource> = resources.iter().map(|r| *r as *const Resource).collect();
        rs.sort_unstable();
        rs.dedup();
        let n = rs.len();
        let reqs = rs
            .iter()
            .map(|r| Request { next: AtomicPtr::new(std::ptr::null_mut()), scheduled: AtomicBool::new(false), res: *r })
            .collect();
        let b = Box::into_raw(Box::new(Beh { head: Head { count: AtomicUsize::new(n + 1), reqs }, payload: Some(payload) }));
        self.outstanding.fetch_add(1, Ordering::AcqRel);
        let head = b as *mut Head;
        let mut free_slots = 1;
        unsafe {
            for i in 0..n {
                let req = (&(*head).reqs)[i..].as_ptr() as *mut Request;
                let res = &*(*req).res;
                let prev = res.last.swap(req, Ordering::AcqRel);
                if prev.is_null() {
                    free_slots += 1;
                } else {
                    let mut k = 0;
                    while !(*prev).scheduled.load(Ordering::Acquire) {
                        spin(&mut k);
                    }
                    (*prev).next.store(head, Ordering::Release);
                }
            }
            for i in 0..n {
                (&(*head).reqs)[i].scheduled.store(true, Ordering::Release);
            }
        }
        if self.resolve(head, free_slots) {
            self.push(head as *mut Beh<P>);
        }
    }

    /// `k` predecessors of `h` are done: is it runnable now?
    fn resolve(&self, h: *mut Head, k: usize) -> bool {
        unsafe { (*h).count.fetch_sub(k, Ordering::AcqRel) == k }
    }

    fn push(&self, b: *mut Beh<P>) {
        if let Err(b) = self.fast.push(Ptr(b)) {
            self.queued.fetch_add(1, Ordering::AcqRel);
            self.ready.lock().unwrap().push_back(b);
        }
        // Wake a sleeper; taking the lock orders this after its last check.
        if self.idle.load(Ordering::Acquire) > 0 {
            let _q = self.ready.lock().unwrap();
            self.cv.notify_one();
        }
    }

    fn pop(&self, q: Option<&mut VecDeque<Ptr<P>>>) -> Option<*mut Beh<P>> {
        if let Some(b) = self.fast.pop() {
            return Some(b.0);
        }
        // The overflow, counted by `queued`.
        if self.queued.load(Ordering::Acquire) == 0 {
            return None;
        }
        let b = match q {
            Some(q) => q.pop_front(),
            None => self.ready.lock().unwrap().pop_front(),
        };
        if b.is_some() {
            self.queued.fetch_sub(1, Ordering::AcqRel);
        }
        b.map(|b| b.0)
    }

    /// A behaviour finished: hand each resource to its successor. The first
    /// successor that becomes runnable is returned, for this worker to run.
    fn release(&self, b: *mut Beh<P>) -> Option<*mut Beh<P>> {
        let mut mine: Option<*mut Beh<P>> = None;
        unsafe {
            let head = b as *mut Head;
            let nreqs = { let reqs = &(*head).reqs; reqs.len() };
            for i in 0..nreqs {
                let req = (&(*head).reqs)[i..].as_ptr() as *mut Request;
                let mut next = (*req).next.load(Ordering::Acquire);
                if next.is_null() {
                    let res = &*(*req).res;
                    if res.last.compare_exchange(req, std::ptr::null_mut(), Ordering::AcqRel, Ordering::Acquire).is_ok() {
                        continue;
                    }
                    // A successor swapped in: wait for it to link.
                    let mut k = 0;
                    loop {
                        next = (*req).next.load(Ordering::Acquire);
                        if !next.is_null() {
                            break;
                        }
                        spin(&mut k);
                    }
                }
                if self.resolve(next, 1) {
                    let nb = next as *mut Beh<P>;
                    if mine.is_none() {
                        mine = Some(nb);
                    } else {
                        self.push(nb);
                    }
                }
            }
            drop(Box::from_raw(b));
        }
        mine
    }

    /// Take a runnable behaviour, spinning a little before sleeping; None
    /// when the pool stops (or, for the main thread, when all is done).
    fn take(&self, main_thread: bool) -> Option<*mut Beh<P>> {
        let done = || self.stop.load(Ordering::Acquire) || main_thread && self.outstanding.load(Ordering::Acquire) == 0;
        // Poll with backoff: a tight loop would keep taking the queue's
        // cache lines from the thread pushing to it.
        for k in 0..12 {
            if done() {
                return None;
            }
            if let Some(b) = self.pop(None) {
                return Some(b);
            }
            for _ in 0..(32u32 << k.min(6)) {
                std::hint::spin_loop();
            }
        }
        let mut q = self.ready.lock().unwrap();
        loop {
            if done() {
                return None;
            }
            if let Some(b) = self.pop(Some(&mut q)) {
                return Some(b);
            }
            self.idle.fetch_add(1, Ordering::AcqRel);
            // A push that saw no sleeper has already made its item visible.
            if let Some(b) = self.pop(Some(&mut q)) {
                self.idle.fetch_sub(1, Ordering::AcqRel);
                return Some(b);
            }
            q = self.cv.wait(q).unwrap();
            self.idle.fetch_sub(1, Ordering::AcqRel);
        }
    }

    fn work<S: Worker<P, Error = E>>(&self, s: &mut S, main_thread: bool) {
        let mut next: Option<*mut Beh<P>> = None;
        loop {
            let b = match next.take() {
                Some(b) => b,
                None => match self.take(main_thread) {
                    Some(b) => b,
                    None => return,
                },
            };
            let r = match unsafe { (*b).payload.as_mut() } {
                Some(p) => s.run(p),
                None => Ok(()),
            };
            if let Err(e) = r {
                let mut slot = self.error.lock().unwrap();
                if slot.is_none() {
                    *slot = Some(e);
                }
                self.stop.store(true, Ordering::Release);
                let _q = self.ready.lock().unwrap();
                self.cv.notify_all();
                return;
            }
            next = self.release(b);
            if self.outstanding.fetch_sub(1, Ordering::AcqRel) == 1 {
                let _q = self.ready.lock().unwrap();
                self.cv.notify_all();
            }
        }
    }

    /// After `main` returns, the calling thread works too until no
    /// behaviour is queued or running; then the workers stop (D31).
    pub fn finish<S: Worker<P, Error = E>>(&self, s: &mut S) -> Result<(), E> {
        self.work(s, true);
        self.stop.store(true, Ordering::Release);
        {
            let _q = self.ready.lock().unwrap();
            self.cv.notify_all();
        }
        for h in self.workers.lock().unwrap().drain(..) {
            let _ = h.join();
        }
        match self.error.lock().unwrap().take() {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    /// Take up to `n` threads for `par` (D69).
    pub fn take_par(&self, n: usize) -> usize {
        let mut got = 0;
        while got < n {
            let cur = self.par_budget.load(Ordering::Relaxed);
            if cur == 0 {
                break;
            }
            if self.par_budget.compare_exchange(cur, cur - 1, Ordering::AcqRel, Ordering::Relaxed).is_ok() {
                got += 1;
            }
        }
        got
    }

    pub fn give_par(&self, n: usize) {
        self.par_budget.fetch_add(n, Ordering::AcqRel);
    }
}

/// Dmitry Vyukov's bounded multi-producer multi-consumer queue: each slot
/// has a sequence number saying whose turn it is, so pushing and popping
/// are one compare-and-swap each, with no lock.
struct Mpmc<T> {
    slots: Box<[(AtomicUsize, std::cell::UnsafeCell<Option<T>>)]>,
    mask: usize,
    head: AtomicUsize,
    tail: AtomicUsize,
}

unsafe impl<T: Send> Sync for Mpmc<T> {}
unsafe impl<T: Send> Send for Mpmc<T> {}

impl<T> Mpmc<T> {
    fn new(cap: usize) -> Self {
        let cap = cap.next_power_of_two();
        Mpmc {
            slots: (0..cap).map(|i| (AtomicUsize::new(i), std::cell::UnsafeCell::new(None))).collect(),
            mask: cap - 1,
            head: AtomicUsize::new(0),
            tail: AtomicUsize::new(0),
        }
    }

    /// False if the queue is full.
    fn push(&self, v: T) -> Result<(), T> {
        let mut pos = self.tail.load(Ordering::Relaxed);
        loop {
            let (seq, cell) = &self.slots[pos & self.mask];
            let s = seq.load(Ordering::Acquire);
            let diff = s as isize - pos as isize;
            if diff == 0 {
                match self.tail.compare_exchange_weak(pos, pos + 1, Ordering::Relaxed, Ordering::Relaxed) {
                    Ok(_) => {
                        unsafe { *cell.get() = Some(v) };
                        seq.store(pos + 1, Ordering::Release);
                        return Ok(());
                    }
                    Err(p) => pos = p,
                }
            } else if diff < 0 {
                return Err(v);
            } else {
                pos = self.tail.load(Ordering::Relaxed);
            }
        }
    }

    fn pop(&self) -> Option<T> {
        let mut pos = self.head.load(Ordering::Relaxed);
        loop {
            let (seq, cell) = &self.slots[pos & self.mask];
            let s = seq.load(Ordering::Acquire);
            let diff = s as isize - (pos + 1) as isize;
            if diff == 0 {
                match self.head.compare_exchange_weak(pos, pos + 1, Ordering::Relaxed, Ordering::Relaxed) {
                    Ok(_) => {
                        let v = unsafe { (*cell.get()).take() };
                        seq.store(pos + self.mask + 1, Ordering::Release);
                        return v;
                    }
                    Err(p) => pos = p,
                }
            } else if diff < 0 {
                return None;
            } else {
                pos = self.head.load(Ordering::Relaxed);
            }
        }
    }
}
