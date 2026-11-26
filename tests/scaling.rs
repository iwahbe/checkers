//! Checking takes time in proportion to the program: a chain of n operators
//! (`1 + 1 + … + 1`) is a tree n deep, and work done again at each level for
//! everything below it makes the time grow with n². And a literal in the
//! program doesn't make checking slower than the work its types need.

use std::path::Path;
use std::process::Command;

/// The types and checks phases' time, in milliseconds, for `check <expr> == n`.
fn check_time(dir: &Path, name: &str, term: &str, op: &str, n: usize, wrap: fn(String) -> String) -> f64 {
    let chain = vec![term; n].join(&format!(" {op} "));
    source_time(dir, name, &format!("module {name}\n\ncheck {} == {n}\n", wrap(chain)))
}

/// The types and checks phases' time, in milliseconds, for module `name`.
fn source_time(dir: &Path, name: &str, source: &str) -> f64 {
    let file = dir.join(format!("{name}.ck"));
    std::fs::write(&file, source).unwrap();
    // The fastest of a few runs: the least disturbed by other tests.
    (0..3)
        .map(|_| {
            let out = Command::new(env!("CARGO_BIN_EXE_ckc"))
                .args(["check", "--no-cache", &format!("{name}.ck")])
                .current_dir(dir)
                .env("CHECKERS_PHASE_TIME", "1")
                .output()
                .expect("run ckc");
            let err = String::from_utf8_lossy(&out.stderr);
            assert!(out.status.success(), "{name}: {err}{}", String::from_utf8_lossy(&out.stdout));
            let prefix = format!("{name}.ck: ");
            let times: Vec<f64> = err
                .lines()
                .filter_map(|l| l.strip_prefix(&prefix))
                .filter(|l| l.starts_with("types ") || l.starts_with("checks "))
                .map(|l| l.split(' ').nth(1).unwrap().parse::<f64>().unwrap())
                .collect();
            assert_eq!(times.len(), 2, "{name}: no phase times in\n{err}");
            times.iter().sum::<f64>()
        })
        .fold(f64::INFINITY, f64::min)
}

/// Four times the operators may take at most ten times as long: quadratic
/// work takes sixteen times. (Linear work takes four to six: code
/// generation's share grows a little faster than the program.)
fn assert_linear(name: &str, term: &str, op: &str, wrap: fn(String) -> String) {
    let dir = std::env::temp_dir().join(format!("checkers-scaling-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let small = check_time(&dir, &format!("{name}1000"), term, op, 1000, wrap);
    let large = check_time(&dir, &format!("{name}4000"), term, op, 4000, wrap);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(large < 10.0 * small.max(20.0), "{name}: 1000 operators took {small:.0} ms, 4000 took {large:.0} ms");
}

#[test]
fn a_chain_of_additions_checks_in_linear_time() {
    assert_linear("add", "1", "+", |c| c);
}

#[test]
fn a_chain_of_concatenations_checks_in_linear_time() {
    assert_linear("concat", "\"a\"", "++", |c| format!("len ({c})"));
}

/// A recursive function building a list of `n` in an accumulator: running
/// it takes n steps, each with the list so far.
const BUILD: &str = "fn build n acc -> r : n~Nat, acc~List Nat, r~List Nat
    decreasing n
    if n == 0 then acc else build (n - 1) (0 :: acc)

";

/// Checking `source(name, n)` for a `large` literal may take at most `factor`
/// times as long as for a `small` one (time below 20 ms doesn't count).
fn assert_literal_costs(name: &str, small: usize, large: usize, factor: f64, source: fn(&str, usize) -> String) {
    let dir = std::env::temp_dir().join(format!("checkers-scaling-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let time = |n: usize| source_time(&dir, &format!("{name}{n}"), &source(&format!("{name}{n}"), n));
    let (t_small, t_large) = (time(small), time(large));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        t_large < factor * t_small.max(20.0),
        "{name}: {small} took {t_small:.0} ms, {large} took {t_large:.0} ms"
    );
}

/// A type that needs a call's value: checking runs the call, each step
/// taking the same time however long the list built so far. Four times the
/// steps may take at most eight times as long: quadratic work takes sixteen.
#[test]
fn running_a_call_while_checking_takes_linear_time() {
    assert_literal_costs("by_type", 2000, 8000, 8.0, |name, n| {
        format!(
            "module {name}\n\n{BUILD}fn pick xs -> t : xs~List Nat, t~Type\n    match xs\n        []     -> Bool\n        _ :: _ -> Nat\n\n\
             export fn by_type -> v : v~pick (build {n} [])\n    0\n"
        )
    });
}

/// A field of a call's result, where no type needs the call's value:
/// checking doesn't run it, so the literal doesn't change the time. (Running
/// it would stop at the unfolding limit, still many times as long.)
#[test]
fn reading_a_field_of_a_call_does_not_run_it() {
    assert_literal_costs("by_field", 2000, 2_000_000, 3.0, |name, n| {
        format!(
            "module {name}\n\nrecord Box\n    value~Nat\n\n{BUILD}fn wrap xs -> r : xs~List Nat, r~Box\n    match xs\n        []     -> Box 0\n        _ :: _ -> Box 1\n\n\
             export fn by_field -> v : v~Nat\n    (wrap (build {n} [])).value\n"
        )
    });
}

/// The peak resident memory, in KB, of `ckc check` on a function adding its
/// argument to itself n times, `x + x + … + x`, and a `check` calling it. `x`
/// is an `Int` of any size, so each `+` tests for small integers: about a
/// block per operator. The peak is the child's high-water mark
/// (`ru_maxrss`), which the kernel reports when it is reaped. `wait4` reaps
/// this child alone, so other tests' children, running at the same time,
/// don't count.
///
/// The allocator, mimalloc, returns freed memory to the system immediately
/// (`MIMALLOC_PURGE_DELAY=0`), so the peak is the memory `ckc` holds. By
/// default it waits 10 ms, and returns it only when it is next called after
/// that: whether the `check`'s code generation, freed when it ends, is still
/// resident when Z3 (whose own allocator can't reuse it) starts proving
/// depends on timing. Over 20 runs each, 4,000 operators peaked anywhere from
/// 298 MB to 373 MB and 8,000 from 501 MB to 532 MB; with the memory returned
/// at once, at 242 MB to 256 MB and 412 MB to 416 MB.
#[cfg(target_os = "linux")]
fn check_peak_kb(dir: &Path, name: &str, n: usize) -> u64 {
    let chain = vec!["x"; n].join(" + ");
    source_usage(dir, name, &format!("module {name}\n\nfn f x -> r : x~Int, r~Int\n    {chain}\n\ncheck f 1 == {n}\n")).1
}

/// The CPU time, in milliseconds, and the peak resident memory, in KB, of
/// `ckc check` on module `name`, as `check_peak_kb` measures them. CPU
/// time, unlike the phases' times, doesn't count waiting for a CPU, so it
/// varies less when other tests are running.
#[cfg(target_os = "linux")]
fn source_usage(dir: &Path, name: &str, source: &str) -> (f64, u64) {
    let file = dir.join(format!("{name}.ck"));
    std::fs::write(&file, source).unwrap();
    let child = Command::new(env!("CARGO_BIN_EXE_ckc"))
        .args(["check", "--no-cache", &format!("{name}.ck")])
        .current_dir(dir)
        .env("MIMALLOC_PURGE_DELAY", "0")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .expect("run ckc");
    let pid = child.id() as libc::pid_t;
    let mut status = 0;
    // SAFETY: `rusage` is plain data; `wait4` writes `status` and `usage`.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    let reaped = loop {
        let r = unsafe { libc::wait4(pid, &mut status, 0, &mut usage) };
        if r != -1 || std::io::Error::last_os_error().kind() != std::io::ErrorKind::Interrupted {
            break r;
        }
    };
    assert_eq!(reaped, pid, "{name}: wait4: {}", std::io::Error::last_os_error());
    // `child` is reaped already: dropping it neither waits nor kills.
    drop(child);
    assert!(libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0, "{name}: ckc failed");
    let ms = |t: libc::timeval| t.tv_sec as f64 * 1000.0 + t.tv_usec as f64 / 1000.0;
    (ms(usage.ru_utime) + ms(usage.ru_stime), usage.ru_maxrss as u64)
}

/// Code generation keeps memory in proportion to the function: Cranelift's
/// SSA builder, given a variable per `let`, keeps a map per variable as long
/// as the function's block count, n² for n additions. 4,000, 8,000 and
/// 16,000 operators peak at 242–256 MB, 412–416 MB and 732–737 MB, and with
/// a variable per `let` at 372–376 MB, 1,160–1,164 MB and 4,243–4,247 MB.
/// A fixed part cancels out of the increments: linear memory adds twice as
/// much for the second 8,000 operators as for the 4,000 before them, n² four
/// times. The second may add at most three times the first (1.83 to 2.04
/// over 20 runs, 3.89 to 3.93 with a variable per `let`).
#[cfg(target_os = "linux")]
#[test]
fn additions_compile_in_linear_memory() {
    let dir = std::env::temp_dir().join(format!("checkers-scaling-{}-memory", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let [small, medium, large] = [4000, 8000, 16000].map(|n| check_peak_kb(&dir, &format!("mem{n}"), n));
    let _ = std::fs::remove_dir_all(&dir);
    let (first, second) = (medium.saturating_sub(small), large.saturating_sub(medium));
    assert!(
        second < 3 * first,
        "4000 operators took {} MB at peak, 8000 took {} MB, 16000 took {} MB: the second 8000 added {:.2} times what the 4000 before them did",
        small / 1024,
        medium / 1024,
        large / 1024,
        second as f64 / first as f64
    );
}

/// A function of n `let`s, each joining a string to the one before. `a{i}`'s
/// value, `x ++ "a" ++ … ++ "a"`, is i deep, and each `let` after it refers
/// to it. Shared, the values take memory in proportion to n; copied for each
/// local that holds one, they took n²/2 (2,000 took 350 MB and 2.8 s to
/// elaborate, 8,000 took 4.6 GB and 44 s). So did the names of every local in
/// scope, kept for each operator's message.
#[cfg(target_os = "linux")]
#[test]
fn a_chain_of_lets_checks_in_linear_time_and_memory() {
    let dir = std::env::temp_dir().join(format!("checkers-scaling-{}-lets", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let sizes = [2000, 4000, 8000];
    // The least of a few runs: the least disturbed by other tests.
    let [a, b, c] = sizes.map(|n| {
        let name = format!("by_let{n}");
        let mut s = format!("module {name}\n\nexport fn f x -> r : x~String, r~String\n    let a0 = x\n");
        for i in 1..=n {
            s += &format!("    let a{i} = a{} ++ \"a\"\n", i - 1);
        }
        s += &format!("    a{n}\n");
        (0..7).map(|_| source_usage(&dir, &name, &s)).fold((f64::INFINITY, u64::MAX), |(t, m), (t2, m2)| (t.min(t2), m.min(m2)))
    });
    let _ = std::fs::remove_dir_all(&dir);
    let mb = |kb: u64| kb as f64 / 1024.0;
    // What each doubling adds to the peak: twice as much the second time for
    // linear memory, four times for quadratic; the fixed part (the standard
    // library) cancels out. The peak moves in the allocator's steps, so up
    // to three times. (2,000 to 4,000 lets add 11 MB to 18 MB, 4,000 to
    // 8,000 16 MB to 26 MB; without sharing, 850 MB and 3,396 MB.)
    let (first, second) = (mb(b.1) - mb(a.1), mb(c.1) - mb(b.1));
    assert!(
        second <= 3.0 * first,
        "peak memory: 2000 to 4000 lets added {first:.0} MB, 4000 to 8000 added {second:.0} MB"
    );
    // Time per instruction grows with the memory a run touches, so what a
    // doubling adds to the time doesn't tell quadratic work from cache
    // misses: four times the lets may take at most four times as long, as
    // linear work with any fixed part does (1.4 to 1.8 times; without
    // sharing, 15 times).
    assert!(c.0 <= 4.0 * a.0, "CPU time: 2000 lets took {:.0} ms, 8000 took {:.0} ms", a.0, c.0);
}
