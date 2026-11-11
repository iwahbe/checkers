//! Golden tests (SPEC §12).
//!
//! tests/parse/NAME.ck  → NAME.out is the syntax tree, followed by any diagnostics.
//! tests/check/NAME.ck  → NAME.out is the parse + lint report.
//! tests/types/NAME.ck  → NAME.out is the full report (type checking included).
//! tests/stage/NAME.ck  → NAME.out is the staged code (`checkers stage`), or the
//!                         report if checking fails (SPEC §8.9).
//! tests/run/NAME.args  → run the program named on its first line (SPEC §13.6);
//!                         NAME.out is its stdout, stderr and exit code, from
//!                         the `ckc` binary (`ckc run --threads 1`).
//! tests/stress/NAME.args → as a run test, but with 8 threads, several times
//!                         (CHECKERS_STRESS_RUNS, default 10); stdout lines are
//!                         compared sorted, since behaviours that share no cown
//!                         may print in any order (SPEC §13.5, D67, D68).
//! tests/json/NAME.ck   → NAME.out is `ckc check --json` on it (§15.5), with
//!                         NAME.overlay (a JSON object, paths relative to the
//!                         repository) as `--overlay` if there is one; the
//!                         repository's path is shown as `$ROOT`.
//! tests/fmt/NAME.ck    → NAME.out is `checkers fmt -` on it: stdout, stderr, exit code
//!                         (`checkers` is built from tools/checkers.ck with `ckc build`).
//! tests/tool/NAME.args → each line runs `checkers` with those arguments (`ckc` is
//!                         this build's); NAME.out is their output.
//! tests/lsp/NAME.session → a session with `checkers lsp` (§15.5), run in tests/lsp:
//!                         `> JSON` sends a message (`$ROOT` is the repository,
//!                         `$TEXT(file)` a file's text as a JSON string), `< N`
//!                         waits for N more messages; NAME.out is every message
//!                         received, in order, and the exit code.
//! tools/, examples/, stdlib/, tests/{types,run,stage,stress}: every .ck file must be
//!                         formatted; every .ck file in the repository must format to a
//!                         fixed point with the same syntax tree (D93).
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

/// A run case as native code: the `ckc` binary in a subprocess (its
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
    let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_ckc"))
        .env("CHECKERS_NO_CACHE", "1")
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
        .expect("run ckc");
    child.stdin.take().unwrap().write_all(&stdin).unwrap();
    let out = child.wait_with_output().unwrap();
    format!(
        "-- stdout\n{}-- stderr\n{}-- exit {}\n",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
        out.status.code().unwrap_or(-1)
    )
}

/// A process's output, as run tests show it.
fn shown(out: &std::process::Output) -> String {
    format!(
        "-- stdout\n{}-- stderr\n{}-- exit {}\n",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
        out.status.code().unwrap_or(-1)
    )
}

/// Run `exe` with `args` and `stdin`.
fn run_with(exe: &Path, args: &[&str], stdin: &[u8], dir: &Path) -> std::process::Output {
    let mut child = std::process::Command::new(exe)
        .args(args)
        .env("CKC", env!("CARGO_BIN_EXE_ckc"))
        .env("CHECKERS_NO_CACHE", "1")
        .env("CHECKERS_THREADS", "1")
        .current_dir(dir)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("run checkers");
    child.stdin.take().unwrap().write_all(stdin).unwrap();
    child.wait_with_output().unwrap()
}

fn compare(root: &Path, out_path: &Path, actual: &str, update: bool, failures: &mut Vec<String>) {
    let expected = fs::read_to_string(out_path).unwrap_or_default();
    if actual != expected {
        if update {
            fs::write(out_path, actual).unwrap();
            println!("updated {}", out_path.strip_prefix(root).unwrap().display());
        } else {
            failures.push(format!(
                "── {} ──\n--- expected\n{expected}\n--- actual\n{actual}",
                out_path.strip_prefix(root).unwrap().display()
            ));
        }
    }
}

/// Every `.ck` file under `dir`, recursively.
fn ck_tree(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = fs::read_dir(dir) else { return };
    let mut paths: Vec<PathBuf> = rd.map(|e| e.unwrap().path()).collect();
    paths.sort();
    for p in paths {
        if p.is_dir() {
            ck_tree(&p, out);
        } else if p.extension().is_some_and(|x| x == "ck") {
            out.push(p);
        }
    }
}

/// The syntax tree, if the file parses.
fn tree(name: &str, text: &str) -> Option<String> {
    let c = checkers::parse_only(name, text);
    c.diags.is_empty().then(|| checkers::syntax::print::module(&c.module))
}

/// The build tool (M11, D95): it checks clean; it builds; `checkers fmt`
/// and `checkers` commands give their golden output; the repository is
/// formatted.
fn build_tool(root: &Path, update: bool, failures: &mut Vec<String>) -> usize {
    let mut count = 1;
    let tools = root.join("tools");
    let main = tools.join("checkers.ck");
    let c = checkers::check_in("checkers.ck", &fs::read_to_string(&main).unwrap(), &tools);
    if !c.diags.is_empty() {
        failures.push(format!("── tools/checkers.ck must be clean ──\n{}", c.report()));
    }
    let exe = std::env::temp_dir().join(format!("checkers-golden-{}-tool", std::process::id()));
    let built = std::process::Command::new(env!("CARGO_BIN_EXE_ckc"))
        .env("CHECKERS_NO_CACHE", "1")
        .args(["build", "tools/checkers.ck", "-o"])
        .arg(&exe)
        .current_dir(root)
        .output()
        .expect("run ckc build");
    if !built.status.success() {
        failures.push(format!("── build tools/checkers.ck ──\n{}", String::from_utf8_lossy(&built.stderr)));
        return count;
    }
    let fmt = |text: &[u8]| run_with(&exe, &["fmt", "-"], text, root);

    for path in ck_files(&root.join("tests").join("fmt")) {
        count += 1;
        let actual = shown(&fmt(&fs::read(&path).unwrap()));
        compare(root, &path.with_extension("out"), &actual, update, failures);
    }
    let tool_dir = root.join("tests").join("tool");
    for path in files_with(&tool_dir, "args") {
        count += 1;
        let mut actual = String::new();
        for line in fs::read_to_string(&path).unwrap().lines() {
            let args: Vec<&str> = line.split_whitespace().collect();
            actual += &format!("$ checkers {line}\n{}", shown(&run_with(&exe, &args, b"", root)));
        }
        compare(root, &path.with_extension("out"), &actual, update, failures);
    }

    let lsp_dir = root.join("tests").join("lsp");
    for path in files_with(&lsp_dir, "session") {
        count += 1;
        let actual = lsp_session(&exe, root, &path);
        compare(root, &path.with_extension("out"), &actual, update, failures);
    }

    // The repository: formatted where it should be; everywhere, formatting
    // is a fixed point that keeps the syntax tree.
    let formatted = ["tools", "examples", "stdlib", "tests/types", "tests/run", "tests/stage", "tests/stress"];
    let mut all = Vec::new();
    for d in ["tools", "examples", "stdlib", "tests"] {
        ck_tree(&root.join(d), &mut all);
    }
    for path in all {
        let rel = path.strip_prefix(root).unwrap();
        let name = rel.display().to_string();
        let text = fs::read(&path).unwrap();
        let once = fmt(&text);
        if !once.status.success() {
            continue; // not lexically valid: tests/check has such files on purpose
        }
        count += 1;
        let twice = fmt(&once.stdout);
        if twice.stdout != once.stdout {
            failures.push(format!("── formatting {name} twice changes it ──"));
        }
        let (a, b) = (String::from_utf8_lossy(&text), String::from_utf8_lossy(&once.stdout));
        if let Some(t) = tree(&name, &a) {
            if tree(&name, &b).as_ref() != Some(&t) {
                failures.push(format!("── formatting {name} changes its syntax tree ──\n{b}"));
            }
        }
        if formatted.iter().any(|d| rel.starts_with(d)) && once.stdout != text {
            failures.push(format!("── {name} is not formatted (`checkers fmt {name}`) ──"));
        }
    }
    let _ = fs::remove_file(&exe);
    count
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

    // `ckc check --json` (§15.5).
    for path in ck_files(&root.join("tests").join("json")) {
        count += 1;
        let rel = path.strip_prefix(root).unwrap().to_string_lossy().to_string();
        let mut cmd = std::process::Command::new(env!("CARGO_BIN_EXE_ckc"));
        cmd.env("CHECKERS_NO_CACHE", "1").current_dir(root).arg("check").arg("--json");
        let overlay = path.with_extension("overlay");
        if overlay.exists() {
            cmd.arg("--overlay").arg(&overlay);
        }
        let out = cmd.arg(&rel).output().expect("run ckc check --json");
        let root_text = root.canonicalize().unwrap().to_string_lossy().to_string();
        let actual = format!("{}-- exit {}\n", String::from_utf8_lossy(&out.stdout), out.status.code().unwrap_or(-1))
            .replace(&root_text, "$ROOT")
            + &String::from_utf8_lossy(&out.stderr);
        let out_path = path.with_extension("out");
        let expected = fs::read_to_string(&out_path).unwrap_or_default();
        if actual != expected {
            if update {
                fs::write(&out_path, &actual).unwrap();
                println!("updated {}", out_path.strip_prefix(root).unwrap().display());
            } else {
                failures.push(format!("── {rel} ──\n--- expected\n{expected}\n--- actual\n{actual}"));
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
        let built = std::process::Command::new(env!("CARGO_BIN_EXE_ckc"))
            .env("CHECKERS_NO_CACHE", "1")
            .args(["build", program, "-o"])
            .arg(&exe)
            .current_dir(root)
            .output()
            .expect("run ckc build");
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

    count += build_tool(root, update, &mut failures);

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

/// Run a `tests/lsp/NAME.session` against `checkers lsp` (§15.5).
fn lsp_session(exe: &Path, root: &Path, path: &Path) -> String {
    use std::io::{BufRead, BufReader, Read};
    use std::sync::mpsc;
    let dir = path.parent().unwrap();
    let root_text = root.canonicalize().unwrap().to_string_lossy().to_string();
    let mut child = std::process::Command::new(exe)
        .arg("lsp")
        .env("CKC", env!("CARGO_BIN_EXE_ckc"))
        .env("CHECKERS_NO_CACHE", "1")
        .env("CHECKERS_THREADS", "1")
        .current_dir(dir)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("run checkers lsp");
    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let (tx, rx) = mpsc::channel::<String>();
    std::thread::spawn(move || {
        let mut r = BufReader::new(stdout);
        loop {
            let mut n = None;
            loop {
                let mut line = String::new();
                if r.read_line(&mut line).unwrap_or(0) == 0 {
                    return;
                }
                let line = line.trim_end();
                if line.is_empty() {
                    break;
                }
                if let Some(v) = line.strip_prefix("Content-Length:") {
                    n = v.trim().parse::<usize>().ok();
                }
            }
            let mut body = vec![0; n.unwrap_or(0)];
            if r.read_exact(&mut body).is_err() {
                return;
            }
            let _ = tx.send(String::from_utf8_lossy(&body).to_string());
        }
    });
    let mut out = String::new();
    let text_of = |name: &str| -> String {
        let t = fs::read_to_string(dir.join(name)).unwrap_or_default();
        checkers::json::string(&t)
    };
    for line in fs::read_to_string(path).unwrap().lines() {
        if let Some(msg) = line.strip_prefix("> ") {
            let mut m = msg.replace("$ROOT", &root_text);
            while let Some(k) = m.find("$TEXT(") {
                let end = k + m[k..].find(')').unwrap();
                let name = m[k + 6..end].to_string();
                m.replace_range(k..=end, &text_of(&name));
            }
            let framed = format!("Content-Length: {}\r\n\r\n{m}", m.len());
            if stdin.write_all(framed.as_bytes()).is_err() {
                out += "-- the server closed its input\n";
                break;
            }
            let _ = stdin.flush();
        } else if let Some(n) = line.strip_prefix("< ") {
            for _ in 0..n.trim().parse::<usize>().unwrap_or(0) {
                match rx.recv_timeout(std::time::Duration::from_secs(60)) {
                    Ok(m) => out += &format!("{}\n", m.replace(&root_text, "$ROOT")),
                    Err(_) => {
                        out += "-- timed out waiting for a message\n";
                        break;
                    }
                }
            }
        }
    }
    drop(stdin);
    let status = child.wait().expect("wait for checkers lsp");
    while let Ok(m) = rx.recv_timeout(std::time::Duration::from_millis(200)) {
        out += &format!("{}\n", m.replace(&root_text, "$ROOT"));
    }
    let mut err = String::new();
    if let Some(mut e) = child.stderr.take() {
        let _ = e.read_to_string(&mut err);
    }
    out + &format!("-- exit {}\n{err}", status.code().unwrap_or(-1))
}
