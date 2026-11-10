// Cost of running a body on a reused fiber (M16):
// `cargo test -p checkers_rt --release --test fiber_cost -- --ignored --nocapture`.
use checkers_rt::fiber::Fiber;

fn noop(_: *mut ()) {}

#[test]
#[ignore]
fn cost() {
    let n = 1_000_000;
    let t = std::time::Instant::now();
    for _ in 0..n {
        let mut f = Fiber::with(noop, std::ptr::null_mut());
        let _ = f.resume();
        Fiber::retire(f);
    }
    let per = t.elapsed().as_nanos() as f64 / n as f64;
    println!("start, run and retire a fiber: {per:.1} ns");
    let t = std::time::Instant::now();
    for _ in 0..n {
        let b: Box<[u64; 8]> = Box::new([0; 8]);
        std::hint::black_box(b);
    }
    println!("a box: {:.1} ns", t.elapsed().as_nanos() as f64 / n as f64);
}
