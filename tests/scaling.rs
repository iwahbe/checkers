//! Checking takes time in proportion to the program: a chain of n operators
//! (`1 + 1 + … + 1`) is a tree n deep, and work done again at each level for
//! everything below it makes the time grow with n².

use std::path::Path;
use std::process::Command;

/// The types and checks phases' time, in milliseconds, for `check <expr> == n`.
fn check_time(dir: &Path, name: &str, term: &str, op: &str, n: usize, wrap: fn(String) -> String) -> f64 {
    let file = dir.join(format!("{name}.ck"));
    let chain = vec![term; n].join(&format!(" {op} "));
    std::fs::write(&file, format!("module {name}\n\ncheck {} == {n}\n", wrap(chain))).unwrap();
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

/// The peak resident memory, in KB, of `ckc check` on `check <chain> == n`:
/// the child's high-water mark (`VmHWM`), read until it exits.
#[cfg(target_os = "linux")]
fn check_peak_kb(dir: &Path, name: &str, n: usize) -> u64 {
    let file = dir.join(format!("{name}.ck"));
    let chain = vec!["1"; n].join(" + ");
    std::fs::write(&file, format!("module {name}\n\ncheck {chain} == {n}\n")).unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_ckc"))
        .args(["check", "--no-cache", &format!("{name}.ck")])
        .current_dir(dir)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .expect("run ckc");
    let status = format!("/proc/{}/status", child.id());
    let mut peak = 0;
    loop {
        // The mark only rises, so the last read before exit is the peak (up
        // to the polling interval, after the code generation that matters).
        if let Ok(s) = std::fs::read_to_string(&status) {
            if let Some(kb) = s.lines().find_map(|l| l.strip_prefix("VmHWM:")) {
                peak = peak.max(kb.trim().trim_end_matches("kB").trim().parse().unwrap());
            }
        }
        if let Some(st) = child.try_wait().unwrap() {
            assert!(st.success(), "{name}: ckc failed");
            return peak;
        }
        std::thread::sleep(std::time::Duration::from_millis(2));
    }
}

/// Code generation keeps memory in proportion to the function: Cranelift's
/// SSA builder, given a variable per `let`, kept a map per variable as long as
/// the function's block count, n² for a chain of n additions (8,000 took
/// 1.2 GB). Four times the operators may take at most three times the memory;
/// quadratic memory took about five.
#[cfg(target_os = "linux")]
#[test]
fn a_chain_of_additions_compiles_in_linear_memory() {
    let dir = std::env::temp_dir().join(format!("checkers-scaling-{}-memory", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let small = check_peak_kb(&dir, "mem2000", 2000);
    let large = check_peak_kb(&dir, "mem8000", 8000);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(large < 3 * small, "2000 operators took {} MB at peak, 8000 took {} MB", small / 1024, large / 1024);
}
