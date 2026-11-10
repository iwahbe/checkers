//! Threads for calls that can't be polled (M16, D113, §13.8): reading
//! regular files and standard input, `waitpid`, running a child to the end.
//! A behaviour that makes such a call parks; the call runs here and wakes
//! it. When every thread is busy another is started, so a waiting call
//! never queues behind another (as Go hands a blocked call's processor on);
//! a thread that has been idle for a while ends.

use std::collections::VecDeque;
use std::sync::{Condvar, Mutex};
use std::time::Duration;

type Job = Box<dyn FnOnce() + Send>;

struct Pool {
    jobs: VecDeque<Job>,
    idle: usize,
}

static POOL: Mutex<Pool> = Mutex::new(Pool { jobs: VecDeque::new(), idle: 0 });
static CV: Condvar = Condvar::new();

/// How long an idle thread waits for work before it ends.
const LINGER: Duration = Duration::from_secs(10);

/// Stack for these threads: jobs are runtime code, not compiled code.
const STACK: usize = 1 << 20;

pub fn submit(job: Job) {
    let mut p = POOL.lock().unwrap_or_else(|e| e.into_inner());
    p.jobs.push_back(job);
    // Enough idle threads for every queued job: wake one.
    if p.idle >= p.jobs.len() {
        CV.notify_one();
        return;
    }
    drop(p);
    std::thread::Builder::new()
        .name("checkers-blocking".into())
        .stack_size(STACK)
        .spawn(serve)
        .unwrap_or_else(|_| crate::prog::fatal("could not start a thread for a blocking call"));
}

fn serve() {
    let mut p = POOL.lock().unwrap_or_else(|e| e.into_inner());
    loop {
        if let Some(job) = p.jobs.pop_front() {
            drop(p);
            job();
            p = POOL.lock().unwrap_or_else(|e| e.into_inner());
            continue;
        }
        p.idle += 1;
        let (q, timeout) = CV.wait_timeout(p, LINGER).unwrap_or_else(|e| e.into_inner());
        p = q;
        p.idle -= 1;
        if timeout.timed_out() && p.jobs.is_empty() {
            return;
        }
    }
}
