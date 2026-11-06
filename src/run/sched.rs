//! The multi-threaded scheduler (M7, SPEC §13.5, D66).
//!
//! Verona's behaviour-oriented concurrency: scheduling a behaviour appends
//! it, in one step, to the queue of every resource it names (cowns for
//! `when`; for `fork` its own future; for `join` the futures it reads and
//! the one it fills). It runs once it is first in all of its queues, and on
//! finishing leaves them, which may make the next ones runnable. Two
//! behaviours sharing a resource therefore run in the order they were
//! scheduled (causal order), and nothing ever waits while holding a
//! resource, so there is no deadlock.

use super::{Behaviour, Io, Machine, RtError, Rt, R};
use std::collections::{HashMap, VecDeque};
use std::sync::atomic::AtomicUsize;
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;

/// Stack for each worker: behaviours may recurse deeply (a long list).
const WORKER_STACK: usize = 256 << 20;

pub struct Shared {
    st: Mutex<State>,
    /// Workers wait here for a runnable behaviour, and the main thread for
    /// the last one to finish.
    cv: Condvar,
    workers: Mutex<Vec<JoinHandle<()>>>,
    /// Threads `par` may still start (D69); the pool size bounds it.
    pub par_budget: AtomicUsize,
}

struct Pending {
    beh: Option<Behaviour>,
    res: Vec<usize>,
    waiting: usize,
}

#[derive(Default)]
struct State {
    next: u64,
    pending: HashMap<u64, Pending>,
    queues: HashMap<usize, VecDeque<u64>>,
    ready: VecDeque<u64>,
    /// Scheduled and not yet finished.
    outstanding: usize,
    /// Workers waiting for a runnable behaviour (only they need waking).
    idle: usize,
    error: Option<RtError>,
    stop: bool,
}

/// The resources a behaviour names, by identity.
fn resources(b: &Behaviour) -> Vec<usize> {
    let mut r: Vec<usize> = match b {
        Behaviour::When(cs, _) => cs.iter().map(|c| Arc::as_ptr(c) as *const () as usize).collect(),
        Behaviour::Fork(f, _) => vec![Arc::as_ptr(f) as *const () as usize],
        Behaviour::Join(fs, _, out) => {
            let mut v: Vec<usize> = fs.iter().map(|f| Arc::as_ptr(f) as *const () as usize).collect();
            v.push(Arc::as_ptr(out) as *const () as usize);
            v
        }
    };
    r.sort_unstable();
    r.dedup();
    r
}

impl Shared {
    /// A pool of `threads` threads: `threads - 1` workers now, and the main
    /// thread once `main` returns (`finish`).
    pub fn start(rt: Arc<Rt>, io: Arc<Mutex<Io>>, threads: usize) -> Arc<Shared> {
        let s = Arc::new(Shared {
            st: Mutex::new(State::default()),
            cv: Condvar::new(),
            workers: Mutex::new(Vec::new()),
            par_budget: AtomicUsize::new(threads.saturating_sub(1)),
        });
        for _ in 1..threads.max(2) {
            let (s2, rt, io) = (s.clone(), rt.clone(), io.clone());
            let h = std::thread::Builder::new()
                .stack_size(WORKER_STACK)
                .spawn(move || {
                    let mut m = Machine::new(rt, io);
                    m.sched = Some(s2.clone());
                    s2.work(&mut m, false);
                })
                .expect("spawn a worker thread");
            s.workers.lock().unwrap().push(h);
        }
        s
    }

    /// Schedule a behaviour (D66).
    pub fn submit(&self, b: Behaviour) {
        let res = resources(&b);
        let mut st = self.st.lock().unwrap();
        let id = st.next;
        st.next += 1;
        let mut waiting = 0;
        for r in &res {
            let q = st.queues.entry(*r).or_default();
            q.push_back(id);
            if q.len() > 1 {
                waiting += 1;
            }
        }
        st.pending.insert(id, Pending { beh: Some(b), res, waiting });
        st.outstanding += 1;
        if waiting == 0 {
            st.ready.push_back(id);
            if st.idle > 0 {
                self.cv.notify_one();
            }
        }
    }

    /// Run behaviours until stopped; the main thread (`main_thread`) also
    /// returns once none is queued or running.
    fn work(&self, m: &mut Machine, main_thread: bool) {
        loop {
            let (id, b) = {
                let mut st = self.st.lock().unwrap();
                loop {
                    if st.stop || main_thread && st.outstanding == 0 {
                        return;
                    }
                    if let Some(id) = st.ready.pop_front() {
                        let b = st.pending.get_mut(&id).and_then(|p| p.beh.take());
                        break (id, b);
                    }
                    st.idle += 1;
                    st = self.cv.wait(st).unwrap();
                    st.idle -= 1;
                }
            };
            let r = match b {
                Some(b) => m.run_behaviour(b, true).map(|_| ()),
                None => Ok(()),
            };
            let mut st = self.st.lock().unwrap();
            if let Err(e) = r {
                if st.error.is_none() {
                    st.error = Some(e);
                }
                st.stop = true;
                self.cv.notify_all();
                return;
            }
            let woken = self.complete(&mut st, id);
            // One worker per behaviour that just became runnable; this one
            // takes the next itself.
            for _ in 1..woken.min(st.idle + 1) {
                self.cv.notify_one();
            }
            if st.outstanding == 0 {
                self.cv.notify_all();
            }
        }
    }

    /// A behaviour finished: it leaves its queues, and the next behaviour in
    /// each becomes runnable once it is first in all of its own. Returns how
    /// many became runnable.
    fn complete(&self, st: &mut State, id: u64) -> usize {
        let mut woken = 0;
        let Some(p) = st.pending.remove(&id) else { return 0 };
        for r in p.res {
            let Some(q) = st.queues.get_mut(&r) else { continue };
            q.pop_front();
            let next = q.front().copied();
            if q.is_empty() {
                st.queues.remove(&r);
            }
            if let Some(n) = next {
                if let Some(np) = st.pending.get_mut(&n) {
                    np.waiting -= 1;
                    if np.waiting == 0 {
                        st.ready.push_back(n);
                        woken += 1;
                    }
                }
            }
        }
        st.outstanding -= 1;
        woken
    }

    /// After `main` returns, its thread `m` works too until no behaviour is
    /// queued or running; then the workers stop (D31).
    pub fn finish(&self, m: &mut Machine) -> R<()> {
        self.work(m, true);
        let mut st = self.st.lock().unwrap();
        st.stop = true;
        let err = st.error.take();
        drop(st);
        self.cv.notify_all();
        for h in self.workers.lock().unwrap().drain(..) {
            let _ = h.join();
        }
        match err {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }
}
