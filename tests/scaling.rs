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

/// The peak resident memory, in KB, of `ckc check` on `check <chain> == n`:
/// the child's high-water mark (`ru_maxrss`), which the kernel reports when
/// it is reaped. `wait4` reaps this child alone, so other tests' children,
/// running at the same time, don't count.
///
/// The allocator, mimalloc, returns freed memory to the system immediately
/// (`MIMALLOC_PURGE_DELAY=0`), so the peak is the memory `ckc` holds. By
/// default it waits 10 ms, and returns it only when it is next called after
/// that: whether the `check`'s code generation, freed when it ends, is still
/// resident when Z3 (whose own allocator can't reuse it) starts proving
/// depends on timing. Over 20 runs each, 2,000 operators peaked at 224 MB or
/// 292 MB and 8,000 at 585 MB or 670 MB; with the memory returned at once, at
/// 192 MB to 195 MB and 549 MB to 550 MB.
#[cfg(target_os = "linux")]
fn check_peak_kb(dir: &Path, name: &str, n: usize) -> u64 {
    let file = dir.join(format!("{name}.ck"));
    let chain = vec!["1"; n].join(" + ");
    std::fs::write(&file, format!("module {name}\n\ncheck {chain} == {n}\n")).unwrap();
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
    usage.ru_maxrss as u64
}

/// Code generation keeps memory in proportion to the function: Cranelift's
/// SSA builder, given a variable per `let`, kept a map per variable as long as
/// the function's block count, n² for a chain of n additions (2,000 took
/// 192 MB, 8,000 took 1.45 GB). Four times the operators may take at most four
/// times the memory, as linear memory with a fixed part does: 2,000 take about
/// 193 MB, 8,000 about 550 MB.
#[cfg(target_os = "linux")]
#[test]
fn a_chain_of_additions_compiles_in_linear_memory() {
    let dir = std::env::temp_dir().join(format!("checkers-scaling-{}-memory", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let small = check_peak_kb(&dir, "mem2000", 2000);
    let large = check_peak_kb(&dir, "mem8000", 8000);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(large < 4 * small, "2000 operators took {} MB at peak, 8000 took {} MB", small / 1024, large / 1024);
}
