//! The interpreter on the shared lock-free scheduler (D66, D77): the
//! scheduler itself is `checkers_rt::sched`, which native code uses too.
//! Each worker thread runs behaviours with a `Machine` of its own.

use super::{Behaviour, Io, Machine, RtError, Rt};
use checkers_rt::sched::{Pool, Worker};
use std::sync::{Arc, Mutex, OnceLock};

pub type Shared = Pool<Behaviour, RtError>;

impl Worker<Behaviour> for Machine {
    type Error = RtError;

    fn run(&mut self, b: &mut Behaviour) -> Result<(), RtError> {
        // The cells stay in `b` (keeping them alive) until the scheduler has
        // released them; run on a copy that holds them too.
        let taken = match b {
            Behaviour::When(cs, f) => Behaviour::When(cs.clone(), std::mem::replace(f, super::Value::Erased)),
            Behaviour::Fork(c, f) => Behaviour::Fork(c.clone(), std::mem::replace(f, super::Value::Erased)),
            Behaviour::Join(cs, f, o) => Behaviour::Join(cs.clone(), std::mem::replace(f, super::Value::Erased), o.clone()),
        };
        self.run_behaviour(taken, true).map(|_| ())
    }
}

/// A pool of `threads` threads whose machines schedule onto the pool itself.
pub fn start(rt: Arc<Rt>, io: Arc<Mutex<Io>>, threads: usize) -> Arc<Shared> {
    let me: Arc<OnceLock<Arc<Shared>>> = Arc::new(OnceLock::new());
    let me2 = me.clone();
    let pool = Pool::start(threads, move || {
        let mut m = Machine::new(rt.clone(), io.clone());
        m.pool_cell = Some(me2.clone());
        m
    });
    let _ = me.set(pool.clone());
    pool
}
