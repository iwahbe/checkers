//! Behaviours of native programs (§13.5): `when`, `fork`, `join`, `par`.
//! With one thread they run on a FIFO queue after `main` returns (D44,
//! D67); otherwise on the lock-free pool (D66, D77).

use crate::apply::apply;
use crate::obj::*;
use crate::prog::*;
use crate::sched::{Pool, Worker};
use crate::word::*;
use std::collections::VecDeque;
use std::sync::{Arc, Mutex, OnceLock};

pub enum Beh {
    When(Vec<Arc<Cell>>, W),
    Fork(Arc<Cell>, W),
    Join(Vec<Arc<Cell>>, W, Arc<Cell>),
}

// Words are shared between threads; ownership is tracked by counts.
unsafe impl Send for Beh {}

pub struct NativeWorker;

impl Worker<Beh> for NativeWorker {
    type Error = ();
    fn run(&mut self, b: &mut Beh) -> Result<(), ()> {
        // The cells stay in `b` until the scheduler has released them.
        run_in_place(b);
        Ok(())
    }
}

static POOL: OnceLock<Arc<Pool<Beh, ()>>> = OnceLock::new();
static FIFO: Mutex<VecDeque<Beh>> = Mutex::new(VecDeque::new());

pub fn start_pool(threads: usize) {
    if threads > 1 {
        let _ = POOL.set(Pool::start(threads, || NativeWorker));
    }
}

fn pool() -> Option<&'static Arc<Pool<Beh, ()>>> {
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
            p.submit(&res, b);
        }
        None => FIFO.lock().unwrap().push_back(b),
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

/// Run one behaviour. `ready`: its futures are filled (always, on the pool).
/// Returns it if a `join` must wait (FIFO only).
fn run(b: Beh, ready: bool) -> Option<Beh> {
    match b {
        Beh::When(cells, f) => {
            let contents: Vec<W> = cells.iter().map(|c| std::mem::replace(&mut *c.v.lock().unwrap(), ERASED)).collect();
            let r = apply(f, contents);
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
        Beh::Fork(fut, f) => {
            let v = apply(f, vec![UNIT]);
            *fut.v.lock().unwrap() = v;
        }
        Beh::Join(futs, f, out) => {
            if !ready && futs.iter().any(|x| *x.v.lock().unwrap() == UNSET) {
                return Some(Beh::Join(futs, f, out));
            }
            let vals: Vec<W> = futs
                .iter()
                .map(|x| {
                    let v = std::mem::replace(&mut *x.v.lock().unwrap(), UNSET);
                    if v == UNSET {
                        ERASED
                    } else {
                        v
                    }
                })
                .collect();
            let v = apply(f, vals);
            *out.v.lock().unwrap() = v;
        }
    }
    None
}

/// Run the FIFO queue until it is empty (D44).
pub fn run_fifo(owner: u32) {
    let mut stalled = 0;
    loop {
        let b = FIFO.lock().unwrap().pop_front();
        let Some(b) = b else { return };
        match run(b, false) {
            Some(waiting) => {
                stalled += 1;
                let mut q = FIFO.lock().unwrap();
                if stalled > q.len() + 1 {
                    drop(q);
                    error(owner, "a `join` waits on a future that is never filled");
                }
                q.push_back(waiting);
            }
            None => stalled = 0,
        }
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
