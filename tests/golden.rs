//! Golden tests (SPEC §12).
//!
//! tests/parse/NAME.ck  → NAME.out is the syntax tree, followed by any diagnostics.
//! tests/check/NAME.ck  → NAME.out is the parse + lint report.
//! tests/types/NAME.ck  → NAME.out is the full report (type checking included).
//! tests/stage/NAME.ck  → NAME.out is the staged code (`checkers stage`), or the
//!                         report if checking fails (SPEC §8.9).
//! tests/run/NAME.args  → run the program named on its first line (SPEC §13.6);
//!                         NAME.out is its stdout, stderr and exit code, from
//!                         the `checkers` binary (`checkers run --threads 1`).
//! tests/stress/NAME.args → as a run test, but with 8 threads, several times
//!                         (CHECKERS_STRESS_RUNS, default 10); stdout lines are
//!                         compared sorted, since behaviours that share no cown
//!                         may print in any order (SPEC §13.5, D67, D68).
//! examples/*.ck        → must check with no errors and no warnings, unless listed
//!                         in examples/PENDING: then tests/pending/NAME.out pins it.
//!
//! `UPDATE_GOLDEN=1 cargo test --test golden` rewrites the .out files.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

fn files_with(dir: &Path, ext: &str) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == ext))
        .collect();
    v.sort();
    v
}

fn ck_files(dir: &Path) -> Vec<PathBuf> {
    files_with(dir, "ck")
}

/// A run case as native code: the `checkers` binary in a subprocess (its
/// runtime writes to the process's streams), in the case's directory.
fn run_native(args_path: &Path, threads: usize) -> String {
    let spec = fs::read_to_string(args_path).unwrap();
    let mut lines = spec.lines();
    let first = lines.next().unwrap_or_default();
    let (flags, program): (Vec<&str>, &str) = match first.strip_prefix("--unverified ") {
        Some(p) => (vec!["--unverified"], p),
        None => (vec![], first),
    };
    let stdin = fs::read(args_path.with_extension("in")).unwrap_or_default();
    let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_checkers"))
        .arg("run")
        .args(["--threads", &threads.to_string()])
        .args(flags)
        .arg(program)
        .args(lines)
        .current_dir(args_path.parent().unwrap())
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("run checkers");
    child.stdin.take().unwrap().write_all(&stdin).unwrap();
    let out = child.wait_with_output().unwrap();
    format!(
        "-- stdout\n{}-- stderr\n{}-- exit {}\n",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
        out.status.code().unwrap_or(-1)
    )
}

/// A run result with its stdout lines sorted.
fn sorted_stdout(out: &str) -> String {
    let (head, rest) = out.split_once("-- stderr\n").unwrap_or((out, ""));
    let mut lines: Vec<&str> = head.strip_prefix("-- stdout\n").unwrap_or(head).lines().collect();
    lines.sort_unstable();
    let mut s = String::from("-- stdout (sorted)\n");
    for l in lines {
        s += l;
        s += "\n";
    }
    s + "-- stderr\n" + rest
}

fn run(path: &Path, mode: &str) -> String {
    let text = fs::read_to_string(path).unwrap();
    let name = path.file_name().unwrap().to_string_lossy().to_string();
    // Imported modules are found beside the test, and shown by their relative path.
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let dir = path.parent().unwrap().strip_prefix(root).unwrap_or(Path::new("")).to_path_buf();
    let c = if mode == "types" || mode == "stage" {
        checkers::check_in(&name, &text, &dir)
    } else {
        checkers::parse_only(&name, &text)
    };
    match mode {
        "parse" => {
            let mut out = checkers::syntax::print::module(&c.module);
            if !c.diags.is_empty() {
                out += "\n";
                out += &c.report();
            }
            out
        }
        // Staged code, or the errors that prevented it.
        "stage" if c.errors() == 0 => c.staged.clone(),
        _ => c.report(),
    }
}

fn main() {
    // Checking recurses deeply: a big stack.
    checkers::with_big_stack(golden);
}

fn golden() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let update = std::env::var_os("UPDATE_GOLDEN").is_some();
    let mut failures = Vec::new();
    let mut count = 0;

    for mode in ["parse", "check", "types", "stage"] {
        for path in ck_files(&root.join("tests").join(mode)) {
            count += 1;
            let actual = run(&path, mode);
            let out_path = path.with_extension("out");
            let expected = fs::read_to_string(&out_path).unwrap_or_default();
            if actual != expected {
                if update {
                    fs::write(&out_path, &actual).unwrap();
                    println!("updated {}", out_path.strip_prefix(root).unwrap().display());
                } else {
                    failures.push(format!(
                        "── {} ──\n--- expected\n{expected}\n--- actual\n{actual}",
                        path.strip_prefix(root).unwrap().display()
                    ));
                }
            }
        }
    }

    let run_dir = root.join("tests").join("run");
    std::env::set_current_dir(&run_dir).unwrap();
    for path in files_with(&run_dir, "args") {
        count += 1;
        let actual = run_native(&path, 1);
        let out_path = path.with_extension("out");
        let expected = fs::read_to_string(&out_path).unwrap_or_default();
        if actual != expected {
            if update {
                fs::write(&out_path, &actual).unwrap();
                println!("updated {}", out_path.strip_prefix(root).unwrap().display());
            } else {
                failures.push(format!(
                    "── {} ──\n--- expected\n{expected}\n--- actual\n{actual}",
                    path.strip_prefix(root).unwrap().display()
                ));
            }
        }
    }

    // Stress tests: every run on many threads must give the same result.
    let stress_dir = root.join("tests").join("stress");
    let runs: usize = std::env::var("CHECKERS_STRESS_RUNS").ok().and_then(|n| n.parse().ok()).unwrap_or(10);
    std::env::set_current_dir(&stress_dir).unwrap();
    for path in files_with(&stress_dir, "args") {
        count += 1;
        let out_path = path.with_extension("out");
        let expected = fs::read_to_string(&out_path).unwrap_or_default();
        let mut seen: Vec<String> = Vec::new();
        for _ in 0..runs.max(1) {
            let actual = sorted_stdout(&run_native(&path, 8));
            if !seen.contains(&actual) {
                seen.push(actual);
            }
        }
        let name = path.strip_prefix(root).unwrap().display().to_string();
        if seen.len() > 1 {
            failures.push(format!("── {name}: {} different results in {runs} runs ──\n{}", seen.len(), seen.join("--- or\n")));
        } else if seen[0] != expected {
            if update {
                fs::write(&out_path, &seen[0]).unwrap();
                println!("updated {}", out_path.strip_prefix(root).unwrap().display());
            } else {
                failures.push(format!("── {name} ──\n--- expected\n{expected}\n--- actual\n{}", seen[0]));
            }
        }
    }
    std::env::set_current_dir(root).unwrap();

    // Executables (`checkers build`): built, then run like a run case.
    for (args_name, program) in [("wc_stdin", "examples/wc.ck"), ("behaviours", "tests/run/behaviours.ck")] {
        count += 1;
        let exe = std::env::temp_dir().join(format!("checkers-golden-{}-{args_name}", std::process::id()));
        let built = std::process::Command::new(env!("CARGO_BIN_EXE_checkers"))
            .args(["build", program, "-o"])
            .arg(&exe)
            .current_dir(root)
            .output()
            .expect("run checkers build");
        if !built.status.success() {
            failures.push(format!("── build {program} ──\n{}", String::from_utf8_lossy(&built.stderr)));
            continue;
        }
        let args_path = run_dir.join(format!("{args_name}.args"));
        let spec = fs::read_to_string(&args_path).unwrap();
        let stdin = fs::read(args_path.with_extension("in")).unwrap_or_default();
        let mut child = std::process::Command::new(&exe)
            .args(spec.lines().skip(1))
            .env("CHECKERS_THREADS", "1")
            .current_dir(&run_dir)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .expect("run the executable");
        child.stdin.take().unwrap().write_all(&stdin).unwrap();
        let out = child.wait_with_output().unwrap();
        let _ = fs::remove_file(&exe);
        let actual = format!(
            "-- stdout\n{}-- stderr\n{}-- exit {}\n",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr),
            out.status.code().unwrap_or(-1)
        );
        let expected = fs::read_to_string(args_path.with_extension("out")).unwrap_or_default();
        if actual != expected {
            failures.push(format!("── built {program} ──\n--- expected\n{expected}\n--- actual\n{actual}"));
        }
    }

    // Examples waiting on a later milestone (D48): their output is pinned instead.
    let pending: Vec<String> = fs::read_to_string(root.join("examples").join("PENDING"))
        .unwrap_or_default()
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .map(|l| l.split_whitespace().next().unwrap_or("").to_string())
        .collect();
    for path in ck_files(&root.join("examples")) {
        count += 1;
        let file = path.file_name().unwrap().to_string_lossy().to_string();
        let text = fs::read_to_string(&path).unwrap();
        let c = checkers::check_in(&file, &text, &root.join("examples"));
        if pending.contains(&file) {
            let out_path = root.join("tests").join("pending").join(Path::new(&file).with_extension("out"));
            let actual = c.report();
            let expected = fs::read_to_string(&out_path).unwrap_or_default();
            if actual != expected {
                if update {
                    fs::create_dir_all(out_path.parent().unwrap()).unwrap();
                    fs::write(&out_path, &actual).unwrap();
                    println!("updated {}", out_path.strip_prefix(root).unwrap().display());
                } else {
                    failures.push(format!("── pending examples/{file} ──\n--- expected\n{expected}\n--- actual\n{actual}"));
                }
            }
        } else if !c.diags.is_empty() {
            failures.push(format!("── examples/{file} must be clean ──\n{}", c.report()));
        }
    }

    // The standard library's own lemmas and postconditions are proven too.
    count += 1;
    let stdlib = checkers::check_stdlib();
    if !stdlib.is_empty() {
        failures.push(format!("── the standard library must verify ──\n{stdlib}"));
    }

    if failures.is_empty() {
        println!("golden: {count} files ok");
    } else {
        for f in &failures {
            println!("{f}");
        }
        println!("golden: {} of {count} failed (UPDATE_GOLDEN=1 to accept)", failures.len());
        std::process::exit(1);
    }
}
