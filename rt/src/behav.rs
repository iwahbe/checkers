//! Behaviours of native programs (§13.5): `when`, `fork`, `join`, `par`.
//! With one thread they run on a FIFO queue after `main` returns (D44,
//! D67); otherwise on the lock-free pool (D66, D77).

use crate::apply::apply;
use crate::obj::*;
use crate::prog::*;
use crate::fiber::{Fiber, Left};
use crate::sched::{Pool, Ran, Worker};
use crate::word::*;
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex, OnceLock};

pub enum Beh {
    When(Vec<Arc<Cell>>, W),
    Fork(Arc<Cell>, W),
    Join(Vec<Arc<Cell>>, W, Arc<Cell>),
}

// Words are shared between threads; ownership is tracked by counts.
unsafe impl Send for Beh {}

/// A behaviour and, once it has started, the fiber it runs on (D113).
pub struct Task {
    beh: Beh,
    fiber: Option<Box<Fiber>>,
}

impl Task {
    fn new(beh: Beh) -> Task {
        Task { beh, fiber: None }
    }

    /// Run until it finishes or waits. The task must not move while it has
    /// a fiber: the fiber refers to its behaviour.
    fn step(&mut self) -> Left {
        if self.fiber.is_none() {
            let b: *mut Beh = &mut self.beh;
            self.fiber = Some(Fiber::with(|b| run_in_place(unsafe { &mut *(b as *mut Beh) }), b as *mut ()));
        }
        let left = self.fiber.as_mut().map_or(Left::Done, |f| f.resume());
        if matches!(left, Left::Done) {
            if let Some(f) = self.fiber.take() {
                Fiber::retire(f);
            }
        }
        left
    }
}

pub struct NativeWorker;

impl Worker<Task> for NativeWorker {
    type Error = ();
    fn run(&mut self, t: &mut Task) -> Result<Ran, ()> {
        // The cells stay in the task until the scheduler has released them.
        Ok(match t.step() {
            Left::Done => Ran::Done,
            Left::Parked(register) => Ran::Parked(register),
        })
    }
}

static POOL: OnceLock<Arc<Pool<Task, ()>>> = OnceLock::new();
/// One thread (D67): the queue. A behaviour that has started and is waiting
/// lives on its fiber's stack, so the queue holds behaviours by value; one
/// that has started carries the cowns it holds.
enum Entry {
    New(Beh),
    Started(Box<Fiber>, Vec<usize>),
}

unsafe impl Send for Entry {}

static FIFO: Mutex<VecDeque<Entry>> = Mutex::new(VecDeque::new());

/// Behaviours that have waited and can go on (with the cowns they hold), and
/// how many are still waiting.
#[allow(clippy::type_complexity)]
static RESUMED: Mutex<(VecDeque<(Box<Fiber>, Vec<usize>)>, usize)> = Mutex::new((VecDeque::new(), 0));
static RESUMED_CV: std::sync::Condvar = std::sync::Condvar::new();
/// Behaviours parked or resumed and not yet run again (read without the lock).
static PARKED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The body of a fiber that owns its behaviour: moved onto the fiber's stack
/// before the first switch back, so the queue's copy can be forgotten.
fn run_owned(b: *mut ()) {
    let mut beh = unsafe { std::ptr::read(b as *const Beh) };
    run_in_place(&mut beh);
}

/// A `join` whose futures aren't all filled yet must wait (FIFO only).
fn waiting(e: &Entry) -> bool {
    matches!(e, Entry::New(Beh::Join(futs, _, _)) if futs.iter().any(|x| *x.v.lock().unwrap() == UNSET))
}

/// The cowns a behaviour holds while it runs, by address.
fn cowns(e: &Entry) -> Vec<usize> {
    match e {
        Entry::New(Beh::When(cells, _)) => cells.iter().map(|c| Arc::as_ptr(c) as usize).collect(),
        Entry::New(_) => Vec::new(),
        Entry::Started(_, cs) => cs.clone(),
    }
}

/// The next behaviour that has finished waiting, waiting for one if `wait`;
/// None when nothing is waiting any more.
fn next_resumed(wait: bool) -> Option<Entry> {
    if !wait && PARKED.load(std::sync::atomic::Ordering::Acquire) == 0 {
        return None;
    }
    let mut r = RESUMED.lock().unwrap();
    loop {
        if let Some((f, cs)) = r.0.pop_front() {
            PARKED.fetch_sub(1, std::sync::atomic::Ordering::AcqRel);
            return Some(Entry::Started(f, cs));
        }
        if r.1 == 0 || !wait {
            return None;
        }
        // Nothing to run until input comes: what was written goes out first.
        drop(r);
        crate::io::flush();
        r = RESUMED.lock().unwrap();
        if r.0.is_empty() && r.1 > 0 {
            r = RESUMED_CV.wait(r).unwrap();
        }
    }
}

/// Run the FIFO queue until it is empty and nothing waits (D44). A behaviour
/// that waits parks, keeping its cowns: a later behaviour on any of them is
/// held back until it finishes, and so is every later one on those (causal
/// order, §8.5). A behaviour that can go on goes to the back of the queue
/// (§13.8).
pub fn run_fifo(owner: u32) {
    let mut stalled = 0;
    // Cowns held by parked behaviours.
    let mut busy: HashMap<usize, usize> = HashMap::new();
    // Behaviours held back for those cowns, in order, with their cowns.
    let mut held_back: VecDeque<(Entry, Vec<usize>)> = VecDeque::new();
    loop {
        // The first held-back behaviour none of whose cowns is busy or wanted
        // by an earlier held-back one.
        let mut picked = None;
        let mut reserved: HashSet<usize> = HashSet::new();
        if !held_back.is_empty() {
            for (i, (_, cs)) in held_back.iter().enumerate() {
                if cs.iter().any(|c| busy.contains_key(c) || reserved.contains(c)) {
                    reserved.extend(cs.iter().copied());
                } else {
                    picked = Some(i);
                    break;
                }
            }
        }
        let e = match picked.and_then(|i| held_back.remove(i)) {
            Some((e, _)) => e,
            None => {
                let next = FIFO.lock().unwrap().pop_front();
                match next {
                    Some(e) => {
                        if matches!(e, Entry::New(Beh::When(..))) && !(busy.is_empty() && reserved.is_empty()) {
                            let cs = cowns(&e);
                            if cs.iter().any(|c| busy.contains_key(c) || reserved.contains(c)) {
                                held_back.push_back((e, cs));
                                continue;
                            }
                        }
                        e
                    }
                    // Nothing queued: wait for a parked behaviour, if there is one.
                    None => match next_resumed(true) {
                        Some(e) => e,
                        None => return,
                    },
                }
            }
        };
        if waiting(&e) {
            stalled += 1;
            let mut q = FIFO.lock().unwrap();
            if stalled > q.len() + 1 {
                drop(q);
                // Only a parked behaviour can still fill a future: wait for it.
                match next_resumed(true) {
                    Some(r) => {
                        let mut q = FIFO.lock().unwrap();
                        q.push_back(r);
                        q.push_back(e);
                        stalled = 0;
                    }
                    None => error(owner, "a `join` waits on a future that is never filled"),
                }
                continue;
            }
            q.push_back(e);
            continue;
        }
        stalled = 0;
        let cs = cowns(&e);
        let started = matches!(e, Entry::Started(..));
        let (fiber, left) = match e {
            Entry::New(beh) => {
                let mut beh = std::mem::ManuallyDrop::new(beh);
                let mut f = Fiber::with(run_owned, &mut *beh as *mut Beh as *mut ());
                let left = f.resume();
                (f, left)
            }
            Entry::Started(mut f, _) => {
                let left = f.resume();
                (f, left)
            }
        };
        match left {
            Left::Done => {
                if started {
                    for c in &cs {
                        if let Some(n) = busy.get_mut(c) {
                            *n -= 1;
                            if *n == 0 {
                                busy.remove(c);
                            }
                        }
                    }
                }
                Fiber::retire(fiber)
            }
            Left::Parked(register) => {
                if !started {
                    for c in &cs {
                        *busy.entry(*c).or_insert(0) += 1;
                    }
                }
                RESUMED.lock().unwrap().1 += 1;
                PARKED.fetch_add(1, std::sync::atomic::Ordering::AcqRel);
                let parked = SendFiber(fiber, cs);
                register(Box::new(move || {
                    let parked = parked;
                    let mut r = RESUMED.lock().unwrap();
                    r.1 -= 1;
                    r.0.push_back((parked.0, parked.1));
                    RESUMED_CV.notify_all();
                }));
            }
        }
        // Behaviours that have finished waiting go to the back of the queue.
        while let Some(r) = next_resumed(false) {
            FIFO.lock().unwrap().push_back(r);
        }
    }
}

struct SendFiber(Box<Fiber>, Vec<usize>);
unsafe impl Send for SendFiber {}

pub fn start_pool(threads: usize) {
    if threads > 1 {
        let _ = POOL.set(Pool::start(threads, || NativeWorker));
    }
}

fn pool() -> Option<&'static Arc<Pool<Task, ()>>> {
    POOL.get()
}

fn schedule(b: Beh) {
    match pool() {
        Some(p) => {
            let res: Vec<&crate::sched::Resource> = match &b {
                Beh::When(cs, _) => cs.iter().map(|c| &c.res).collect(),
                Beh::Fork(f, _) => vec![&f.res],
                Beh::Join(fs, _, out) => fs.iter().map(|c| &c.res).chain(std::iter::once(&out.res)).collect(),
            };
            // The cells outlive the behaviour: it holds them.
            let res: Vec<&'static crate::sched::Resource> = res.into_iter().map(|r| unsafe { &*(r as *const _) }).collect();
            p.submit(&res, Task::new(b));
        }
        None => FIFO.lock().unwrap().push_back(Entry::New(b)),
    }
}

/// Run a behaviour on the pool, leaving its cells in it.
fn run_in_place(b: &mut Beh) {
    match b {
        Beh::When(cells, f) => {
            let contents: Vec<W> = cells.iter().map(|c| std::mem::replace(&mut *c.v.lock().unwrap(), ERASED)).collect();
            let r = apply(std::mem::replace(f, ERASED), contents);
            store_when(cells, r);
        }
        Beh::Fork(fut, f) => {
            let v = apply(std::mem::replace(f, ERASED), vec![UNIT]);
            *fut.v.lock().unwrap() = v;
        }
        Beh::Join(futs, f, out) => {
            let vals: Vec<W> = futs.iter().map(|x| take_future(x)).collect();
            let v = apply(std::mem::replace(f, ERASED), vals);
            *out.v.lock().unwrap() = v;
        }
    }
}

fn take_future(x: &Cell) -> W {
    let v = std::mem::replace(&mut *x.v.lock().unwrap(), UNSET);
    if v == UNSET {
        ERASED
    } else {
        v
    }
}

fn store_when(cells: &[Arc<Cell>], r: W) {
    if cells.len() == 1 {
        *cells[0].v.lock().unwrap() = r;
    } else {
        if !is_kind(r, K_TUPLE) {
            bug("`when` body must return a tuple");
        }
        for (i, c) in cells.iter().enumerate() {
            *c.v.lock().unwrap() = dup(slot(r, i));
        }
        drop_w(r);
    }
}

pub fn finish_pool() {
    if let Some(p) = pool() {
        let _ = p.finish(&mut NativeWorker);
    }
}

fn cells_of(t: W, what: &str) -> Vec<Arc<Cell>> {
    let items: Vec<W> = if is_kind(t, K_TUPLE) { (0..nfields(t)).map(|i| slot(t, i)).collect() } else { vec![t] };
    items
        .into_iter()
        .map(|w| match obj(w) {
            Some(Obj::Cown(c)) if what == "cowns" => c.clone(),
            Some(Obj::Future(c)) if what == "futures" => c.clone(),
            _ => bug(&format!("expected {what}")),
        })
        .collect()
}

/// `when x = c, … using sched: f` (borrowed arguments).
#[no_mangle]
pub extern "C" fn ck_when(cowns: W, f: W) -> W {
    schedule(Beh::When(cells_of(cowns, "cowns"), dup(f)));
    UNIT
}

#[no_mangle]
pub extern "C" fn ck_fork(f: W) -> W {
    let fut = new_cell(UNSET);
    schedule(Beh::Fork(fut.clone(), dup(f)));
    new_obj(Obj::Future(fut))
}

#[no_mangle]
pub extern "C" fn ck_join(futs: W, f: W) -> W {
    let out = new_cell(UNSET);
    schedule(Beh::Join(cells_of(futs, "futures"), dup(f), out.clone()));
    new_obj(Obj::Future(out))
}

struct Send2(W);
unsafe impl Send for Send2 {}

/// `par (e1, …, en)` (D69): `thunks` are closures taking `()`; they are
/// consumed. Components run on threads while the pool has room.
#[no_mangle]
/// # Safety
/// Called by native code with valid pointers (D72).
pub unsafe extern "C" fn ck_par(thunks: *const W, n: u64) -> W {
    let ts: Vec<W> = unsafe { std::slice::from_raw_parts(thunks, n as usize) }.to_vec();
    let spawned = pool().map_or(0, |p| p.take_par(ts.len().saturating_sub(1)));
    let mut out = Vec::with_capacity(ts.len());
    if spawned == 0 {
        for t in ts {
            out.push(apply(t, vec![UNIT]));
        }
        return new_tuple(&out);
    }
    let (first, rest) = ts.split_at(spawned);
    std::thread::scope(|sc| {
        let hs: Vec<_> = first
            .iter()
            .map(|t| {
                let t = Send2(*t);
                let trap = crate::prog::current_trap();
                std::thread::Builder::new()
                    .stack_size(crate::sched::WORKER_STACK)
                    .spawn_scoped(sc, move || {
                        let t = t;
                        crate::prog::set_trap(trap);
                        Send2(apply(t.0, vec![UNIT]))
                    })
                    .expect("spawn a `par` thread")
            })
            .collect();
        let mine: Vec<W> = rest.iter().map(|t| apply(*t, vec![UNIT])).collect();
        for h in hs {
            out.push(h.join().unwrap_or_else(|_| fatal("a `par` thread failed")).0);
        }
        out.extend(mine);
    });
    if let Some(p) = pool() {
        p.give_par(spawned);
    }
    new_tuple(&out)
}
