//! Golden tests (SPEC §12).
//!
//! tests/parse/NAME.ck  → NAME.out is the syntax tree, followed by any diagnostics.
//! tests/check/NAME.ck  → NAME.out is the parse + lint report.
//! tests/types/NAME.ck  → NAME.out is the full report (type checking included).
//! tests/stage/NAME.ck  → NAME.out is the staged code (`checkers stage`), or the
//!                         report if checking fails (SPEC §8.9).
//! tests/run/NAME.args  → run the program named on its first line (SPEC §13.6);
//!                         NAME.out is its stdout, stderr and exit code, from
//!                         the `ckc` binary (`ckc run --threads 1`), with the
//!                         environment variables NAME.env sets (`VAR=value` lines).
//! tests/stress/NAME.args → as a run test, but with 8 threads, several times
//!                         (CHECKERS_STRESS_RUNS, default 10); stdout lines are
//!                         compared sorted, since behaviours that share no cown
//!                         may print in any order (SPEC §13.5, D67, D68).
//! tests/complete/NAME.ck → each `‸` in it is a cursor: NAME.out is what
//!                         `ckc complete` offers there (§15.5, D142), readably.
//! tests/json/NAME.ck   → NAME.out is `ckc check --json` on it (§15.5), with
//!                         NAME.overlay (a JSON object, paths relative to the
//!                         repository) as `--overlay` if there is one; the
//!                         repository's path is shown as `$ROOT`.
//! tests/corpus/NAME.ck → NAME.out is `ckc check` on it with CHECKERS_SMT_CORPUS
//!                         (§7.2): the report, the entries written, then each
//!                         query of module NAME and Z3's answer, in name order.
//! tests/fmt/NAME.ck    → NAME.out is `checkers fmt -` on it: stdout, stderr, exit code
//!                         (`checkers` is built from tools/checkers.ck with `ckc build`).
//! tests/tool/NAME.args → each line runs `checkers` with those arguments (`ckc` is
//!                         this build's); NAME.out is their output.
//! tests/doc/NAME/     → a package (`.ck` files): NAME.out is `ckc doc` on each
//!                         file, then every page `checkers doc` writes for it
//!                         (with a checkers.json, `checkers doc .` run in NAME/);
//!                         with an index.md, a site: every file `checkers site`
//!                         writes (§15.6).
//! tests/lsp/NAME.session → a session with `checkers lsp` (§15.5), run in tests/lsp:
//!                         `> JSON` sends a message (`$ROOT` is the repository,
//!                         `$TEXT(file)` a file's text as a JSON string), `< N`
//!                         waits for N more messages; NAME.out is every message
//!                         received, in order, and the exit code. A session
//!                         waits for each check's diagnostics (a message per
//!                         phase with any) before its next request: they arrive
//!                         whenever the check gets to them, and the server
//!                         sends nothing after answering `shutdown`.
//! tools/, examples/, bench/, stdlib/, smt/, tests/{types,run,stage,stress}: every .ck file must be
//!                         formatted; every .ck file in the repository must format to a
//!                         fixed point with the same syntax tree (D93).
//! examples/*.ck, bench/*.ck → must check with no errors and no warnings.
//! smt/*.ck             → the solver package (#72): each module, its command `main.ck`
//!                         too, checks with no errors and no warnings.
//! tests/smt/NAME.smt2  → NAME.out is what `smt/main.ck parse` writes for it: the
//!                         query written back, or the error reading it (line and column).
//! site/*.md, README.md, the standard library's documentation → `checkers site`
//!                         and `checkers doc` give no warnings: links resolve, code
//!                         blocks compile and run (D148).
//!
//! The cases run in parallel, on CHECKERS_GOLDEN_THREADS threads (default: one
//! per core); failures are reported in the order above.
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
    // `NAME.env`: a variable to set on each line, `NAME=VALUE`.
    let vars = fs::read_to_string(args_path.with_extension("env")).unwrap_or_default();
    let vars = vars.lines().filter_map(|l| l.split_once('='));
    let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_ckc"))
        .env("CHECKERS_NO_CACHE", "1")
        .envs(vars)
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

fn json_str(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o += "\\\"",
            '\\' => o += "\\\\",
            '\n' => o += "\\n",
            c if (c as u32) < 0x20 => o += &format!("\\u{:04x}", c as u32),
            c => o.push(c),
        }
    }
    o + "\""
}

/// A `ckc complete` line, readably: the range replaced, then each candidate
/// as its label, class and the first line of its detail.
fn complete_line(l: &str) -> String {
    let field = |k: &str| -> Option<String> {
        let key = format!("\"{k}\":");
        let i = l.find(&key)? + key.len();
        let rest = &l[i..];
        if rest.starts_with("null") {
            return None;
        }
        if let Some(r) = rest.strip_prefix('"') {
            let mut out = String::new();
            let mut chars = r.chars();
            while let Some(c) = chars.next() {
                match c {
                    '"' => break,
                    '\\' => match chars.next() {
                        Some('n') => out.push('\n'),
                        Some(c) => out.push(c),
                        None => break,
                    },
                    c => out.push(c),
                }
            }
            return Some(out);
        }
        Some(rest.split([',', '}']).next().unwrap_or("").to_string())
    };
    match field("kind").as_deref() {
        Some("complete") => {
            let span = |k: &str| {
                let key = format!("\"{k}\":[");
                let i = l.find(&key).unwrap() + key.len();
                let v: Vec<usize> = l[i..].split(']').next().unwrap().split(',').map(|n| n.parse::<usize>().unwrap() + 1).collect();
                format!("{}:{}", v[0], v[1])
            };
            format!("replaces {}-{}\n", span("start"), span("end"))
        }
        Some("candidate") => {
            let detail = field("detail").unwrap_or_default();
            let detail = detail.lines().next().unwrap_or("");
            let doc = if field("doc").is_some() { "  (documented)" } else { "" };
            format!("  {:<18} {:<15} {detail}{doc}\n", field("label").unwrap_or_default(), field("class").unwrap_or_default())
        }
        Some("done") => String::new(),
        _ => format!("{l}\n"),
    }
}

fn compare(root: &Path, out_path: &Path, actual: &str, update: bool, failures: &mut Vec<String>) {
    compare_as(root, out_path, out_path, actual, update, failures);
}

/// `compare`, the test named by another of its files (`named`) in a failure.
fn compare_as(root: &Path, named: &Path, out_path: &Path, actual: &str, update: bool, failures: &mut Vec<String>) {
    let expected = fs::read_to_string(out_path).unwrap_or_default();
    if actual != expected {
        if update {
            fs::write(out_path, actual).unwrap();
            println!("updated {}", out_path.strip_prefix(root).unwrap().display());
        } else {
            failures.push(format!(
                "── {} ──\n--- expected\n{expected}\n--- actual\n{actual}",
                named.strip_prefix(root).unwrap().display()
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

/// The build tool (M11, D95): it builds; `checkers fmt` and `checkers`
/// commands give their golden output; the repository is formatted. The
/// cases that run `checkers` are added as jobs once it is built.
fn build_tool(pool: &Pool, root: &'static Path, update: bool) -> Outcome {
    let exe = std::env::temp_dir().join(format!("checkers-golden-{}-tool", std::process::id()));
    let built = std::process::Command::new(env!("CARGO_BIN_EXE_ckc"))
        .env("CHECKERS_NO_CACHE", "1")
        .args(["build", "tools/checkers.ck", "-o"])
        .arg(&exe)
        .current_dir(root)
        .output()
        .expect("run ckc build");
    if !built.status.success() {
        return (0, vec![format!("── build tools/checkers.ck ──\n{}", String::from_utf8_lossy(&built.stderr))]);
    }
    let exe = std::sync::Arc::new(Removed(exe));
    let rel = |p: &Path| p.strip_prefix(root).unwrap_or(p).display().to_string();
    // Reported in this order (keys from 2: 0 and 1 are the check and the build).
    let mut jobs: Vec<(String, Task)> = Vec::new();
    // Started first: the site takes longest.
    let mut first: Vec<(String, Task)> = Vec::new();

    for path in ck_files(&root.join("tests").join("fmt")) {
        let exe = exe.clone();
        jobs.push((
            rel(&path),
            Box::new(move |_: &Pool| {
                let mut failures = Vec::new();
                let actual = shown(&fmt(&exe.0, &fs::read(&path).unwrap(), root));
                compare(root, &path.with_extension("out"), &actual, update, &mut failures);
                (1, failures)
            }),
        ));
    }
    for path in files_with(&root.join("tests").join("tool"), "args") {
        let exe = exe.clone();
        jobs.push((
            rel(&path),
            Box::new(move |_: &Pool| {
                let mut failures = Vec::new();
                let mut actual = String::new();
                for line in fs::read_to_string(&path).unwrap().lines() {
                    let args: Vec<&str> = line.split_whitespace().collect();
                    actual += &format!("$ checkers {line}\n{}", shown(&run_with(&exe.0, &args, b"", root)));
                }
                compare(root, &path.with_extension("out"), &actual, update, &mut failures);
                (1, failures)
            }),
        ));
    }

    // Documentation (§15.6): a package's `ckc doc` lines and the pages
    // `checkers doc` writes; a site's pages and llms.txt.
    let doc_dir = root.join("tests").join("doc");
    let mut cases: Vec<PathBuf> = fs::read_dir(&doc_dir).map(|rd| rd.map(|e| e.unwrap().path()).filter(|p| p.is_dir()).collect()).unwrap_or_default();
    cases.sort();
    for case in cases {
        let exe = exe.clone();
        let doc_dir = doc_dir.clone();
        jobs.push((rel(&case), Box::new(move |_: &Pool| (1, doc_case(&exe.0, root, &doc_dir, &case, update)))));
    }

    for path in files_with(&root.join("tests").join("lsp"), "session") {
        let exe = exe.clone();
        jobs.push((
            rel(&path),
            Box::new(move |_: &Pool| {
                let mut failures = Vec::new();
                let actual = lsp_session(&exe.0, root, &path);
                compare(root, &path.with_extension("out"), &actual, update, &mut failures);
                (1, failures)
            }),
        ));
    }

    // The repository: formatted where it should be; everywhere, formatting
    // is a fixed point that keeps the syntax tree.
    let mut all = Vec::new();
    for d in ["tools", "examples", "bench", "stdlib", "smt", "tests"] {
        ck_tree(&root.join(d), &mut all);
    }
    for path in all {
        let exe = exe.clone();
        jobs.push((rel(&path), Box::new(move |_: &Pool| formatted(&exe.0, root, &path))));
    }

    // The site, the README and the standard library's documentation: their
    // links resolve and their code compiles (and runs) with no warnings (D148 e).
    for (i, what) in ["site/", "README.md", "the standard library's documentation"].into_iter().enumerate() {
        let exe = exe.clone();
        first.push((what.to_string(), Box::new(move |_: &Pool| literate_clean(&exe.0, root, i, what))));
    }

    let n = jobs.len();
    let keyed = |j: Vec<(String, Task)>, from: usize| j.into_iter().enumerate().map(move |(i, (name, t))| ((9, from + i), name, t));
    let mut queue: Vec<(Key, String, Task)> = keyed(first, 2 + n).collect();
    queue.extend(keyed(jobs, 2));
    pool.add_first(queue);
    (0, Vec::new())
}

fn fmt(exe: &Path, text: &[u8], root: &Path) -> std::process::Output {
    run_with(exe, &["fmt", "-"], text, root)
}

/// A `tests/doc/NAME/` case (§15.6).
fn doc_case(exe: &Path, root: &Path, doc_dir: &Path, case: &Path, update: bool) -> Vec<String> {
    let mut failures = Vec::new();
    let name = case.file_name().unwrap().to_string_lossy().to_string();
    let rel = case.strip_prefix(root).unwrap().display().to_string();
    let out = std::env::temp_dir().join(format!("checkers-golden-{}-doc-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&out);
    let out_s = out.display().to_string();
    let mut actual = String::new();
    // A package with a manifest is documented from its own directory,
    // as `.`, and named by its manifest.
    let named = case.join("checkers.json").exists();
    let result = if case.join("index.md").exists() {
        run_with(exe, &["site", &rel, "-o", &out_s], b"", root)
    } else {
        let mut sources = Vec::new();
        ck_tree(case, &mut sources);
        for src in sources {
            let src_rel = src.strip_prefix(root).unwrap().display().to_string();
            let o = std::process::Command::new(env!("CARGO_BIN_EXE_ckc")).args(["doc", &src_rel]).current_dir(root).output().unwrap();
            actual += &format!("$ ckc doc {src_rel}\n{}", shown(&o));
        }
        if named {
            run_with(exe, &["doc", ".", "-o", &out_s], b"", case)
        } else {
            run_with(exe, &["doc", &rel, "-o", &out_s, "--name", &name], b"", root)
        }
    };
    let command = if case.join("index.md").exists() {
        format!("site {rel} -o OUT")
    } else if named {
        format!("doc . -o OUT  (in {rel})")
    } else {
        format!("doc {rel} -o OUT")
    };
    actual += &format!("$ checkers {command}\n{}", shown(&result));
    let mut written = Vec::new();
    let mut stack = vec![out.clone()];
    while let Some(d) = stack.pop() {
        for e in fs::read_dir(&d).into_iter().flatten() {
            let p = e.unwrap().path();
            if p.is_dir() {
                stack.push(p);
            } else {
                written.push(p);
            }
        }
    }
    written.sort();
    for p in written {
        let text = fs::read_to_string(&p).unwrap();
        actual += &format!("== OUT/{}\n{text}", p.strip_prefix(&out).unwrap().display());
    }
    let _ = fs::remove_dir_all(&out);
    compare(root, &doc_dir.join(format!("{name}.out")), &actual.replace(&out_s, "OUT"), update, &mut failures);
    failures
}

/// One `.ck` file of the repository: formatting it twice changes nothing
/// more, keeps its syntax tree, and, where the repository must be
/// formatted, changes nothing at all.
fn formatted(exe: &Path, root: &Path, path: &Path) -> Outcome {
    const FORMATTED: [&str; 9] = ["tools", "examples", "bench", "stdlib", "smt", "tests/types", "tests/run", "tests/stage", "tests/stress"];
    let mut failures = Vec::new();
    let rel = path.strip_prefix(root).unwrap();
    let name = rel.display().to_string();
    let text = fs::read(path).unwrap();
    let once = fmt(exe, &text, root);
    if !once.status.success() {
        return (0, failures); // not lexically valid: tests/check has such files on purpose
    }
    let twice = fmt(exe, &once.stdout, root);
    if twice.stdout != once.stdout {
        failures.push(format!("── formatting {name} twice changes it ──"));
    }
    let (a, b) = (String::from_utf8_lossy(&text), String::from_utf8_lossy(&once.stdout));
    if let Some(t) = tree(&name, &a) {
        if tree(&name, &b).as_ref() != Some(&t) {
            failures.push(format!("── formatting {name} changes its syntax tree ──\n{b}"));
        }
    }
    if FORMATTED.iter().any(|d| rel.starts_with(d)) && once.stdout != text {
        failures.push(format!("── {name} is not formatted (`checkers fmt {name}`) ──"));
    }
    (1, failures)
}

/// The site (0), the README (1) or the standard library's documentation (2):
/// no warnings (D148 e).
fn literate_clean(exe: &Path, root: &Path, which: usize, what: &str) -> Outcome {
    let tmp = std::env::temp_dir().join(format!("checkers-golden-{}-literate-{which}", std::process::id()));
    let _ = fs::remove_dir_all(&tmp);
    fs::create_dir_all(&tmp).unwrap();
    let out = tmp.join("out").display().to_string();
    let args: Vec<String> = match which {
        0 => vec!["site".into(), "site".into(), "-o".into(), out],
        1 => {
            fs::create_dir_all(tmp.join("readme")).unwrap();
            fs::copy(root.join("README.md"), tmp.join("readme").join("index.md")).unwrap();
            vec!["site".into(), tmp.join("readme").display().to_string(), "-o".into(), out]
        }
        _ => vec!["doc".into(), "stdlib".into(), "-o".into(), out, "--name".into(), "std".into()],
    };
    let args: Vec<&str> = args.iter().map(|a| a.as_str()).collect();
    let o = run_with(exe, &args, b"", root);
    let _ = fs::remove_dir_all(&tmp);
    if !o.status.success() || !o.stderr.is_empty() {
        return (1, vec![format!("── {what} must have no warnings (D148) ──\n{}", String::from_utf8_lossy(&o.stderr))]);
    }
    (1, Vec::new())
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

/// Held while checking in this process: evaluating `check`s installs the
/// runtime's program descriptor, one per process, so two checks evaluated
/// at once would read each other's. Subprocesses don't need it.
static IN_PROCESS: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn in_process<T>(f: impl FnOnce() -> T) -> T {
    let _held = IN_PROCESS.lock().unwrap_or_else(|e| e.into_inner());
    f()
}

fn run(path: &Path, mode: &str) -> String {
    let text = fs::read_to_string(path).unwrap();
    let name = path.file_name().unwrap().to_string_lossy().to_string();
    // Imported modules are found beside the test, and shown by their relative path.
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let dir = path.parent().unwrap().strip_prefix(root).unwrap_or(Path::new("")).to_path_buf();
    let c = if mode == "types" || mode == "stage" {
        in_process(|| checkers::check_in(&name, &text, &dir))
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
    // Checking recurses deeply: a big stack (each worker has one too).
    checkers::with_big_stack(golden);
}

/// What a job reports: how many cases it ran, and their failures.
type Outcome = (usize, Vec<String>);
type Task = Box<dyn FnOnce(&Pool) -> Outcome + Send>;

/// Where a job's failures are reported: its section, then its place in it.
type Key = (usize, usize);

/// The cases as jobs, run by several threads. A job can add jobs: the cases
/// that need `checkers` wait for its build. Jobs that check in this process
/// run one at a time (`in_process`), and take no worker while they wait.
/// Failures are reported in the order of their keys, whatever order the
/// jobs finish in.
#[derive(Default)]
struct Pool {
    state: std::sync::Mutex<PoolState>,
    ready: std::sync::Condvar,
}

#[derive(Default)]
struct PoolState {
    queue: std::collections::VecDeque<(Key, String, Task)>,
    /// Jobs that check in this process; `local_busy` while one runs.
    local: std::collections::VecDeque<(Key, String, Task)>,
    local_busy: bool,
    running: usize,
    outcomes: Vec<(Key, Outcome)>,
}

impl Pool {
    fn lock(&self) -> std::sync::MutexGuard<'_, PoolState> {
        self.state.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Add a job after those waiting.
    fn add(&self, key: Key, name: String, task: impl FnOnce(&Pool) -> Outcome + Send + 'static) {
        self.lock().queue.push_back((key, name, Box::new(task)));
        self.ready.notify_one();
    }

    /// Add a job that checks in this process.
    fn add_local(&self, key: Key, name: String, task: impl FnOnce(&Pool) -> Outcome + Send + 'static) {
        self.lock().local.push_back((key, name, Box::new(task)));
        self.ready.notify_one();
    }

    /// Add jobs before those waiting, in this order.
    fn add_first(&self, jobs: Vec<(Key, String, Task)>) {
        let mut st = self.lock();
        for job in jobs.into_iter().rev() {
            st.queue.push_front(job);
        }
        drop(st);
        self.ready.notify_all();
    }

    /// Run every job, and every job they add, on `threads` threads.
    fn run(&self, threads: usize) -> Outcome {
        std::thread::scope(|s| {
            for _ in 0..threads.max(1) {
                std::thread::Builder::new().stack_size(1 << 30).spawn_scoped(s, || self.work()).expect("spawn a golden worker");
            }
        });
        let mut outcomes = std::mem::take(&mut self.lock().outcomes);
        outcomes.sort_by_key(|(k, _)| *k);
        let count = outcomes.iter().map(|(_, (n, _))| n).sum();
        (count, outcomes.into_iter().flat_map(|(_, (_, f))| f).collect())
    }

    fn work(&self) {
        loop {
            let mut st = self.lock();
            let (local, (key, name, task)) = loop {
                if !st.local_busy {
                    if let Some(job) = st.local.pop_front() {
                        st.local_busy = true;
                        st.running += 1;
                        break (true, job);
                    }
                }
                if let Some(job) = st.queue.pop_front() {
                    st.running += 1;
                    break (false, job);
                }
                if st.running == 0 {
                    return;
                }
                st = self.ready.wait(st).unwrap_or_else(|e| e.into_inner());
            };
            drop(st);
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| task(self))).unwrap_or_else(|p| {
                let why = p.downcast_ref::<&str>().map(|s| s.to_string()).or_else(|| p.downcast_ref::<String>().cloned()).unwrap_or_default();
                (1, vec![format!("── {name} panicked ──\n{why}\n")])
            });
            let mut st = self.lock();
            st.running -= 1;
            st.outcomes.push((key, outcome));
            if local {
                st.local_busy = false;
            }
            if local || (st.running == 0 && st.queue.is_empty()) {
                self.ready.notify_all();
            }
        }
    }
}

/// A file removed when the last job using it is done.
struct Removed(PathBuf);

impl Drop for Removed {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn golden() {
    let root: &'static Path = Path::new(env!("CARGO_MANIFEST_DIR"));
    let update = std::env::var_os("UPDATE_GOLDEN").is_some();
    let threads = std::env::var("CHECKERS_GOLDEN_THREADS")
        .ok()
        .and_then(|n| n.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()));
    let pool = Pool::default();
    let rel = |p: &Path| p.strip_prefix(root).unwrap_or(p).display().to_string();

    // The longest jobs start first: the build of `checkers` (the site waits
    // for it), the stress tests, the standard library.
    pool.add((9, 1), "build tools/checkers.ck".into(), move |pool| build_tool(pool, root, update));

    // Stress tests: every run on many threads must give the same result.
    let runs: usize = std::env::var("CHECKERS_STRESS_RUNS").ok().and_then(|n| n.parse().ok()).unwrap_or(10);
    for (i, path) in files_with(&root.join("tests").join("stress"), "args").into_iter().enumerate() {
        pool.add((7, i), rel(&path), move |_| {
            let mut failures = Vec::new();
            let mut seen: Vec<String> = Vec::new();
            for _ in 0..runs.max(1) {
                let actual = sorted_stdout(&run_native(&path, 8));
                if !seen.contains(&actual) {
                    seen.push(actual);
                }
            }
            if seen.len() > 1 {
                let name = path.strip_prefix(root).unwrap().display();
                failures.push(format!("── {name}: {} different results in {runs} runs ──\n{}", seen.len(), seen.join("--- or\n")));
            } else {
                compare_as(root, &path, &path.with_extension("out"), &seen[0], update, &mut failures);
            }
            (1, failures)
        });
    }

    // The standard library's own lemmas and postconditions are proven too.
    pool.add_local((11, 0), "the standard library".into(), |_| {
        let stdlib = in_process(checkers::check_stdlib);
        (1, if stdlib.is_empty() { vec![] } else { vec![format!("── the standard library must verify ──\n{stdlib}")] })
    });

    pool.add_local((9, 0), "check tools/checkers.ck".into(), move |_| {
        let tools = root.join("tools");
        let c = in_process(|| checkers::check_in("checkers.ck", &fs::read_to_string(tools.join("checkers.ck")).unwrap(), &tools));
        (1, if c.diags.is_empty() { vec![] } else { vec![format!("── tools/checkers.ck must be clean ──\n{}", c.report())] })
    });

    for (m, mode) in ["parse", "check", "types", "stage"].into_iter().enumerate() {
        for (i, path) in ck_files(&root.join("tests").join(mode)).into_iter().enumerate() {
            let name = rel(&path);
            let job = move |_: &Pool| {
                let mut failures = Vec::new();
                compare_as(root, &path, &path.with_extension("out"), &run(&path, mode), update, &mut failures);
                (1, failures)
            };
            if mode == "types" || mode == "stage" {
                pool.add_local((m, i), name, job);
            } else {
                pool.add((m, i), name, job);
            }
        }
    }

    // `ckc complete` (§15.5, D142): each `‸` in the file is a cursor.
    for (i, path) in ck_files(&root.join("tests").join("complete")).into_iter().enumerate() {
        pool.add((4, i), rel(&path), move |_| {
            let mut failures = Vec::new();
            let rel = path.strip_prefix(root).unwrap().to_string_lossy().to_string();
            let marked = fs::read_to_string(&path).unwrap();
            let text = marked.replace('‸', "");
            let mut actual = String::new();
            let mut removed = 0;
            for (at, _) in marked.match_indices('‸') {
                let at = at - removed;
                removed += '‸'.len_utf8();
                let line = text[..at].matches('\n').count();
                let col = at - text[..at].rfind('\n').map_or(0, |i| i + 1);
                let overlay = format!("{{{}:{}}}", json_str(&rel), json_str(&text));
                let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_ckc"))
                    .env("CHECKERS_NO_CACHE", "1")
                    .current_dir(root)
                    .args(["complete", "--overlay", "-", &rel, &line.to_string(), &col.to_string()])
                    .stdin(std::process::Stdio::piped())
                    .stdout(std::process::Stdio::piped())
                    .stderr(std::process::Stdio::piped())
                    .spawn()
                    .expect("run ckc complete");
                use std::io::Write as _;
                child.stdin.take().unwrap().write_all(overlay.as_bytes()).unwrap();
                let out = child.wait_with_output().unwrap();
                actual += &format!("== line {}, column {}\n", line + 1, col + 1);
                for l in String::from_utf8_lossy(&out.stdout).lines() {
                    actual += &complete_line(l);
                }
                actual += &String::from_utf8_lossy(&out.stderr);
            }
            compare(root, &path.with_extension("out"), &actual, update, &mut failures);
            (1, failures)
        });
    }

    // `ckc check --json` (§15.5).
    for (i, path) in ck_files(&root.join("tests").join("json")).into_iter().enumerate() {
        pool.add((5, i), rel(&path), move |_| {
            let mut failures = Vec::new();
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
            compare_as(root, &path, &path.with_extension("out"), &actual, update, &mut failures);
            (1, failures)
        });
    }

    // `CHECKERS_SMT_CORPUS` (§7.2): the report, then the queries written for
    // the program's own module and Z3's answers, in name order.
    for (i, path) in ck_files(&root.join("tests").join("corpus")).into_iter().enumerate() {
        pool.add((12, i), rel(&path), move |_| {
            let mut failures = Vec::new();
            let rel = path.strip_prefix(root).unwrap().to_string_lossy().to_string();
            let module = path.file_stem().unwrap().to_string_lossy().to_string();
            let dir = std::env::temp_dir().join(format!("checkers-golden-{}-corpus-{module}", std::process::id()));
            let _ = fs::remove_dir_all(&dir);
            let out = std::process::Command::new(env!("CARGO_BIN_EXE_ckc"))
                .env("CHECKERS_SMT_CORPUS", &dir)
                .current_dir(root)
                .args(["check", "--no-cache", &rel])
                .output()
                .expect("run ckc check");
            let mut actual = format!("{}{}-- exit {}\n", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr), out.status.code().unwrap_or(-1));
            let mut names: Vec<String> = fs::read_dir(&dir).map(|rd| rd.map(|e| e.unwrap().file_name().to_string_lossy().to_string()).collect()).unwrap_or_default();
            names.sort();
            actual += &format!("-- written: {}\n", names.join(", "));
            let own = dir.join(&module);
            for f in if own.is_dir() { files_with(&own, "smt2") } else { Vec::new() } {
                for g in [f.clone(), f.with_extension("z3")] {
                    actual += &format!("== {module}/{}\n{}", g.file_name().unwrap().to_string_lossy(), fs::read_to_string(&g).unwrap_or_else(|_| "(missing)\n".into()));
                }
            }
            let _ = fs::remove_dir_all(&dir);
            compare_as(root, &path, &path.with_extension("out"), &actual, update, &mut failures);
            (1, failures)
        });
    }

    let run_dir = root.join("tests").join("run");
    for (i, path) in files_with(&run_dir, "args").into_iter().enumerate() {
        pool.add((6, i), rel(&path), move |_| {
            let mut failures = Vec::new();
            compare_as(root, &path, &path.with_extension("out"), &run_native(&path, 1), update, &mut failures);
            (1, failures)
        });
    }

    // Executables (`checkers build`): built, then run like a run case.
    for (i, (args_name, program)) in [("wc_stdin", "examples/wc.ck"), ("behaviours", "tests/run/behaviours.ck")].into_iter().enumerate() {
        let run_dir = run_dir.clone();
        pool.add((8, i), format!("build {program}"), move |_| {
            let exe = Removed(std::env::temp_dir().join(format!("checkers-golden-{}-{args_name}", std::process::id())));
            let built = std::process::Command::new(env!("CARGO_BIN_EXE_ckc"))
                .env("CHECKERS_NO_CACHE", "1")
                .args(["build", program, "-o"])
                .arg(&exe.0)
                .current_dir(root)
                .output()
                .expect("run ckc build");
            if !built.status.success() {
                return (1, vec![format!("── build {program} ──\n{}", String::from_utf8_lossy(&built.stderr))]);
            }
            let args_path = run_dir.join(format!("{args_name}.args"));
            let spec = fs::read_to_string(&args_path).unwrap();
            let stdin = fs::read(args_path.with_extension("in")).unwrap_or_default();
            let mut child = std::process::Command::new(&exe.0)
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
            let actual = format!(
                "-- stdout\n{}-- stderr\n{}-- exit {}\n",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr),
                out.status.code().unwrap_or(-1)
            );
            let expected = fs::read_to_string(args_path.with_extension("out")).unwrap_or_default();
            (1, if actual == expected { vec![] } else { vec![format!("── built {program} ──\n--- expected\n{expected}\n--- actual\n{actual}")] })
        });
    }

    let mut i = 0;
    for dir in ["examples", "bench"] {
        for path in ck_files(&root.join(dir)) {
            pool.add_local((10, i), rel(&path), move |_| {
                let file = path.file_name().unwrap().to_string_lossy().to_string();
                let text = fs::read_to_string(&path).unwrap();
                let c = in_process(|| checkers::check_in(&file, &text, &root.join(dir)));
                (1, if c.diags.is_empty() { vec![] } else { vec![format!("── {dir}/{file} must be clean ──\n{}", c.report())] })
            });
            i += 1;
        }
    }

    smt_package(&pool, root, update);

    let start = std::time::Instant::now();
    let (count, failures) = pool.run(threads);
    let took = start.elapsed().as_secs_f64();
    if failures.is_empty() {
        println!("golden: {count} files ok ({took:.0}s on {threads} threads)");
    } else {
        for f in &failures {
            println!("{f}");
        }
        println!("golden: {} of {count} failed (UPDATE_GOLDEN=1 to accept)", failures.len());
        std::process::exit(1);
    }
}

/// The solver package (#72): its modules check clean; its command builds;
/// `main parse` gives each `tests/smt/*.smt2` case's output; `main` answers
/// each `tests/smt/answer/*.smt2`; `main compare` gives `tests/smt/compare/compare.out`.
fn smt_package(pool: &Pool, root: &'static Path, update: bool) {
    let pkg = root.join("smt");
    for (i, path) in ck_files(&pkg).into_iter().enumerate() {
        let pkg = pkg.clone();
        let name = path.strip_prefix(root).unwrap().display().to_string();
        pool.add_local((13, i), name.clone(), move |_| {
            let file = path.file_name().unwrap().to_string_lossy().to_string();
            let c = in_process(|| checkers::check_in(&file, &fs::read_to_string(&path).unwrap(), &pkg));
            (1, if c.diags.is_empty() { vec![] } else { vec![format!("── {name} must be clean ──\n{}", c.report())] })
        });
    }
    pool.add((14, 0), "build smt/main.ck".into(), move |_| {
        let mut failures = Vec::new();
        let exe = Removed(std::env::temp_dir().join(format!("checkers-golden-{}-smt", std::process::id())));
        let built = std::process::Command::new(env!("CARGO_BIN_EXE_ckc"))
            .env("CHECKERS_NO_CACHE", "1")
            .args(["build", "smt/main.ck", "-o"])
            .arg(&exe.0)
            .current_dir(root)
            .output()
            .expect("run ckc build");
        if !built.status.success() {
            return (1, vec![format!("── build smt/main.ck ──\n{}", String::from_utf8_lossy(&built.stderr))]);
        }
        let mut count = 1;
        for path in files_with(&root.join("tests").join("smt"), "smt2") {
            count += 1;
            let actual = shown(&run_with(&exe.0, &["parse"], &fs::read(&path).unwrap(), root));
            compare(root, &path.with_extension("out"), &actual, update, &mut failures);
        }
        // `main` answers each `tests/smt/answer/*.smt2` as `z3 -in` would.
        for path in files_with(&root.join("tests").join("smt").join("answer"), "smt2") {
            count += 1;
            let actual = shown(&run_with(&exe.0, &[], &fs::read(&path).unwrap(), root));
            compare(root, &path.with_extension("out"), &actual, update, &mut failures);
        }
        // `main compare` on a small corpus, with a stand-in for `z3`.
        count += 1;
        let changed = Removed(std::env::temp_dir().join(format!("checkers-golden-{}-changed", std::process::id())));
        let saved = Removed(std::env::temp_dir().join(format!("checkers-golden-{}-saved", std::process::id())));
        let dir = "tests/smt/compare";
        let out = run_with(
            &exe.0,
            &[
                "compare",
                "--z3",
                &format!("{dir}/fake-z3"),
                "--baseline",
                &format!("{dir}/baseline"),
                "--changed",
                &changed.0.to_string_lossy(),
                "--save",
                &saved.0.to_string_lossy(),
                &format!("{dir}/corpus"),
            ],
            b"",
            root,
        );
        let actual = format!(
            "{}-- changed\n{}-- saved\n{}",
            shown(&out),
            fs::read_to_string(&changed.0).unwrap_or_default(),
            fs::read_to_string(&saved.0).unwrap_or_default()
        );
        compare(root, &root.join(dir).join("compare.out"), &actual, update, &mut failures);
        (count, failures)
    });
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
