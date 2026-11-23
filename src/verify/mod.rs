//! The prover pipeline (SPEC §7, M3): obligations → SMT-LIB → Z3 → diagnostics
//! and the trust ledger.

pub mod smt;

use crate::core::{quote, show};
use crate::diag::Diagnostic;
use crate::elab::{Elab, ObKind, Obligation, Probe, ProbeKind, WeakenRole};
use crate::source::Span;

/// One entry of the trust ledger (§7.4).
#[derive(Clone, Debug)]
pub struct LedgerEntry {
    pub span: Span,
    pub how: &'static str,
    pub what: String,
    pub hash: Option<u64>,
}

pub struct Verified {
    pub diags: Vec<Diagnostic>,
    pub ledger: Vec<LedgerEntry>,
    pub z3_version: Option<String>,
    pub proved: usize,
    /// Z3 answers asked for, and how many came from the cache (D100).
    pub asked: usize,
    pub reused: usize,
}

enum Answer {
    Unsat,
    Sat(String),
    Unknown(String),
}

/// Z3 reports API misuse through an error handler; the default one may exit
/// the process. SMT-LIB errors come back in the output text instead.
unsafe extern "C" fn ignore_error(_: z3_sys::Z3_context, _: z3_sys::Z3_error_code) {}

/// The linked-in Z3's version (D46): the release, the same for every build
/// of it (some builds' full version names a commit too).
pub fn z3_version() -> Option<String> {
    let (mut major, mut minor, mut build, mut rev) = (0, 0, 0, 0);
    // SAFETY: writes four integers.
    unsafe { z3_sys::Z3_get_version(&mut major, &mut minor, &mut build, &mut rev) };
    Some(format!("Z3 {major}.{minor}.{build}.{rev}"))
}

/// Z3's work limit per query (D101): unlike a timeout, it gives the same
/// answer on every machine and at any load. Twice the work the hardest
/// answer in the repository needs (a counterexample in `tests/run/echo.ck`,
/// 3 050 000, 11/10/2026); the hardest proof needs 154 000.
pub const RLIMIT: u64 = 6_000_000;

/// The work limit for the weaker queries tried first (§7.2): a shortcut,
/// so giving up on one only costs this much before the next. 1.5 times the
/// hardest proof they give in the repository (660 000; the next is 255 000).
pub const QUICK_RLIMIT: u64 = 1_000_000;
/// For asking whether a branch can run (D144 d): a contradiction among the
/// facts is found quickly or not at all, and there is one query per branch.
pub const PROBE_RLIMIT: u64 = 200_000;

/// The work limit each query is tried with first (D154): nearly every
/// answer in the repository needs far less (all but 0.2%), and a query that
/// can't prove its goal often searches until its limit, so giving up costs
/// this before the next query.
pub const FIRST_RLIMIT: u64 = 200_000;

/// A weaker query, tried first: with the smaller work limit.
fn quick(q: Option<String>) -> Option<String> {
    q.map(|t| with_limit(&t, QUICK_RLIMIT))
}

/// A query with another work limit.
fn with_limit(t: &str, limit: u64) -> String {
    t.replacen(&format!("(set-option :rlimit {RLIMIT})"), &format!("(set-option :rlimit {limit})"), 1)
}

/// A wall-clock cap, in case Z3 is slow to use up its work limit. An answer
/// it cuts off depends on the machine, so it isn't cached.
pub const SAFETY_MS: u64 = 60_000;

/// Where Z3's answers are cached (D100), if anywhere.
static CACHE: std::sync::Mutex<Option<std::path::PathBuf>> = std::sync::Mutex::new(None);

/// The queries one stage of proving asked (a module's preparation, its
/// solving, its diagnostics): each one's text, as a hash and length, and
/// whether its answer came from the disk cache (D100). Stages of different
/// modules run at once, so the answers reused are counted afterwards, in
/// module order (`tally`): the count is the same however the stages interleave.
#[derive(Default)]
struct Log(std::sync::Mutex<Vec<(u64, usize, bool)>>);

impl Log {
    fn note(&self, query: &str, from_disk: bool) {
        self.0.lock().unwrap_or_else(|e| e.into_inner()).push((fnv(query), query.len(), from_disk));
    }
}

/// How many queries the stages asked, and how many of their answers were
/// reused: from the disk cache, or asked before in this process (as if
/// the stages had run one after another, in the order given).
fn tally(logs: &[&Log]) -> (usize, usize) {
    static SEEN: std::sync::Mutex<Option<std::collections::HashSet<(u64, usize)>>> = std::sync::Mutex::new(None);
    let mut seen = SEEN.lock().unwrap_or_else(|e| e.into_inner());
    let seen = seen.get_or_insert_with(Default::default);
    let (mut asked, mut reused) = (0, 0);
    for log in logs {
        for &(h, n, from_disk) in log.0.lock().unwrap_or_else(|e| e.into_inner()).iter() {
            asked += 1;
            let new = seen.insert((h, n));
            if from_disk || !new {
                reused += 1;
            }
        }
    }
    (asked, reused)
}

/// How many Z3 contexts solve at once: the pool's threads.
fn solvers() -> usize {
    std::thread::available_parallelism().map_or(2, |n| n.get()).min(8)
}

/// Cache Z3's answers in `dir` (`None`: don't).
pub fn set_cache(dir: Option<std::path::PathBuf>) {
    *CACHE.lock().unwrap_or_else(|e| e.into_inner()) = dir;
}

fn cache_dir() -> Option<std::path::PathBuf> {
    CACHE.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

// ── Verified modules (D143) ─────────────────────────────────────────────────

/// What a module verified before contributes: its part of the trust ledger
/// and how many obligations it proved.
#[derive(Clone)]
pub struct Remembered {
    pub ledger: Vec<LedgerEntry>,
    pub proved: usize,
    pub z3_version: Option<String>,
    /// Its proofs phase's warnings (W022, D144).
    pub warnings: Vec<Diagnostic>,
}

/// Where verified modules are remembered, if anywhere: beside Z3's answers,
/// unless the prover is being watched.
pub fn modules_dir() -> Option<std::path::PathBuf> {
    if std::env::var_os("CHECKERS_SMT_DUMP").is_some() || std::env::var_os("CHECKERS_SMT_TIME").is_some() {
        return None;
    }
    cache_dir().map(|d| d.join("modules"))
}

const MODULE_HEADER: &str = "checkers module 2";

/// The module verified under `key`, if it was.
pub fn remembered(key: &str) -> Option<Remembered> {
    let text = std::fs::read_to_string(modules_dir()?.join(key)).ok()?;
    let mut lines = text.lines();
    if lines.next()? != MODULE_HEADER {
        return None;
    }
    let proved = lines.next()?.strip_prefix("proved ")?.parse().ok()?;
    let z3 = lines.next()?.strip_prefix("z3 ")?;
    let z3_version = (z3 != "-").then(|| z3.to_string());
    let mut ledger = Vec::new();
    let mut warnings = Vec::new();
    for l in lines {
        if let Some(w) = l.strip_prefix("warning ") {
            warnings.push(unflatten(w)?);
            continue;
        }
        let mut parts = l.splitn(5, ' ');
        let start: u32 = parts.next()?.parse().ok()?;
        let end: u32 = parts.next()?.parse().ok()?;
        let how = match parts.next()? {
            "trusted" => "trusted",
            "axiom" => "axiom",
            "computed" => "computed",
            "smt" => "smt",
            _ => return None,
        };
        let hash = match parts.next()? {
            "-" => None,
            h => Some(u64::from_str_radix(h, 16).ok()?),
        };
        let what = parts.next()?.replace("\\n", "\n");
        ledger.push(LedgerEntry { span: Span { start, end }, how, what, hash });
    }
    Some(Remembered { ledger, proved, z3_version, warnings })
}

/// A warning on one line: `CODE START END` and its texts, separated by
/// U+001F, newlines escaped.
fn flatten(d: &Diagnostic) -> String {
    let esc = |t: &str| t.replace('\\', "\\\\").replace('\n', "\\n").replace('\u{1f}', " ");
    let mut parts = vec![esc(&d.message), esc(d.label.as_deref().unwrap_or("")), esc(d.help.as_deref().unwrap_or(""))];
    parts.extend(d.notes.iter().map(|n| esc(n)));
    format!("{} {} {} {}", d.code, d.span.start, d.span.end, parts.join("\u{1f}"))
}

fn unflatten(line: &str) -> Option<Diagnostic> {
    let mut it = line.splitn(4, ' ');
    let code = match it.next()? {
        "W022" => "W022",
        _ => return None,
    };
    let start = it.next()?.parse().ok()?;
    let end = it.next()?.parse().ok()?;
    let unesc = |t: &str| {
        let mut out = String::new();
        let mut cs = t.chars();
        while let Some(c) = cs.next() {
            match (c, c == '\\') {
                (_, true) => match cs.next() {
                    Some('n') => out.push('\n'),
                    Some(x) => out.push(x),
                    None => {}
                },
                (c, false) => out.push(c),
            }
        }
        out
    };
    let parts: Vec<String> = it.next()?.split('\u{1f}').map(unesc).collect();
    let mut d = Diagnostic::warning(code, parts.first()?.clone(), Span { start, end });
    if let Some(l) = parts.get(1).filter(|l| !l.is_empty()) {
        d = d.with_label(l.clone());
    }
    if let Some(h) = parts.get(2).filter(|h| !h.is_empty()) {
        d = d.with_help(h.clone());
    }
    for n in parts.iter().skip(3) {
        d = d.with_note(n.clone());
    }
    Some(d)
}

/// Remember that the module under `key` verified with `v`.
pub fn remember(key: &str, v: &Verified) {
    let Some(dir) = modules_dir() else { return };
    if std::fs::create_dir_all(&dir).is_err() {
        return;
    }
    let mut out = format!("{MODULE_HEADER}\nproved {}\nz3 {}\n", v.proved, v.z3_version.as_deref().unwrap_or("-"));
    for x in &v.ledger {
        let hash = x.hash.map(|h| format!("{h:x}")).unwrap_or_else(|| "-".into());
        out += &format!("{} {} {} {hash} {}\n", x.span.start, x.span.end, x.how, x.what.replace('\n', "\\n"));
    }
    for d in v.diags.iter().filter(|d| d.code == "W022") {
        out += &format!("warning {}\n", flatten(d));
    }
    // Written whole, then renamed: a reader never sees half of it.
    let tmp = dir.join(format!("{key}.{}", std::process::id()));
    if std::fs::write(&tmp, out).is_ok() {
        let _ = std::fs::rename(&tmp, dir.join(key));
    }
}

/// A 128-bit digest, as hex: two different 64-bit hashes of `s`.
pub fn digest(s: &str) -> String {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    s.hash(&mut h);
    format!("{:016x}{:016x}", fnv(s), h.finish())
}

/// A cache entry: a header with Z3's version and the query's length, the
/// query in full (compared on a hit, so a hash collision can't reuse a wrong
/// answer), then Z3's output.
fn cache_path(dir: &std::path::Path, version: &str, query: &str) -> std::path::PathBuf {
    dir.join("z3").join(format!("{:016x}", fnv(&format!("{version}\n{query}"))))
}

fn cached(query: &str) -> Option<String> {
    let dir = cache_dir()?;
    let version = z3_version()?;
    let data = std::fs::read_to_string(cache_path(&dir, &version, query)).ok()?;
    let (header, rest) = data.split_once('\n')?;
    let (v, n) = header.strip_prefix("checkers z3 cache 1 ")?.rsplit_once(' ')?;
    let n: usize = n.parse().ok()?;
    (v == version && rest.get(..n)? == query).then(|| rest[n..].to_string())
}

fn store(query: &str, out: &str) {
    let (Some(dir), Some(version)) = (cache_dir(), z3_version()) else { return };
    let path = cache_path(&dir, &version, query);
    let Some(parent) = path.parent() else { return };
    if std::fs::create_dir_all(parent).is_err() {
        return;
    }
    // Whole or not at all: write elsewhere, then rename.
    let tmp = path.with_extension(format!("tmp{}", std::process::id()));
    let data = format!("checkers z3 cache 1 {version} {}\n{query}{out}", query.len());
    if std::fs::write(&tmp, data).is_ok() {
        let _ = std::fs::rename(&tmp, &path);
    }
}

/// Z3's answer to one SMT-LIB script, from the cache or a fresh Z3 context.
fn ask(query: &str, log: &Log) -> Answer {
    ask_all(&[Some(query.to_string())], log).pop().flatten().unwrap_or_else(|| Answer::Unknown("Z3 could not start".into()))
}

/// Z3's output for a query asked before: in this process, or on disk (D100,
/// `true`).
fn known(query: &str) -> Option<(String, bool)> {
    // The same query asked twice in this process: Z3's answer depends only
    // on the text, so it is reused (D154).
    if let Some(out) = MEMO.lock().unwrap_or_else(|e| e.into_inner()).as_ref().and_then(|m| m.get(query)).cloned() {
        return Some((out, false));
    }
    cached(query).map(|out| (out, true))
}

static MEMO: std::sync::Mutex<Option<std::collections::HashMap<String, String>>> = std::sync::Mutex::new(None);

/// Z3's output for a query not asked before, from a fresh Z3 context; kept
/// for the next time it is asked.
fn fresh(query: &str) -> String {
    let start = std::time::Instant::now();
    let timed = std::env::var_os("CHECKERS_SMT_TIME").is_some();
    // Timed, Z3's statistics follow its output, for the work it used;
    // they are cut off before the output is read or stored.
    let mut out = if timed { run_z3(&format!("{query}(get-info :all-statistics)\n")) } else { run_z3(query) };
    let mut used = String::from("?");
    if timed {
        if let Some(at) = out.rfind("(:") {
            used = out[at..].split(":rlimit-count").nth(1).and_then(|r| r.split_whitespace().next()).unwrap_or("?").trim_end_matches(')').to_string();
            out.truncate(at);
        }
    }
    // `CHECKERS_SMT_TIME=1`: each query Z3 answered, its time, size,
    // answer, work limit and the work it used.
    if timed {
        let what = query.lines().find(|l| l.starts_with("(assert (not")).unwrap_or("").chars().take(120).collect::<String>();
        let said = out.split_whitespace().next().unwrap_or("?");
        let limit = query.split("(set-option :rlimit ").nth(1).and_then(|r| r.split(')').next()).unwrap_or("?");
        eprintln!("smt {:>6} ms {:>7} bytes {said:>7} rlimit {limit:>8} used {used:>8} {what}", start.elapsed().as_millis(), query.len());
        if let Some(err) = out.lines().find(|l| l.starts_with("(error")) {
            eprintln!("smt error {err}");
        }
    }
    let cut_off = out.starts_with("unknown") && start.elapsed().as_millis() as u64 >= SAFETY_MS * 9 / 10;
    if !cut_off {
        store(query, &out);
        MEMO.lock().unwrap_or_else(|e| e.into_inner()).get_or_insert_with(Default::default).insert(query.to_string(), out.clone());
    }
    out
}

/// The threads Z3 runs on: `solvers()` of them for the whole process,
/// shared by every module being proved, each with a big stack (Z3 recurses
/// deeply on large terms). Kept, not started for each batch of queries:
/// Z3 allocates heavily, and a thread's allocator caches stay warm.
struct Pool {
    jobs: std::sync::Mutex<std::collections::VecDeque<Job>>,
    ready: std::sync::Condvar,
}

/// A query for the pool, and where its output goes.
type Job = (usize, String, std::sync::mpsc::Sender<(usize, String)>);

/// The pool, if any of its threads started.
fn pool() -> Option<&'static Pool> {
    static POOL: std::sync::OnceLock<Pool> = std::sync::OnceLock::new();
    static STARTED: std::sync::Once = std::sync::Once::new();
    static WORKING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
    let p: &'static Pool = POOL.get_or_init(|| Pool { jobs: Default::default(), ready: Default::default() });
    STARTED.call_once(|| {
        let mut any = false;
        for _ in 0..solvers() {
            let worker = std::thread::Builder::new().stack_size(512 << 20).spawn(move || loop {
                let (i, query, done) = {
                    let mut jobs = p.jobs.lock().unwrap_or_else(|e| e.into_inner());
                    loop {
                        match jobs.pop_front() {
                            Some(j) => break j,
                            None => jobs = p.ready.wait(jobs).unwrap_or_else(|e| e.into_inner()),
                        }
                    }
                };
                let _ = done.send((i, fresh(&query)));
            });
            any |= worker.is_ok();
        }
        WORKING.store(any, std::sync::atomic::Ordering::Relaxed);
    });
    WORKING.load(std::sync::atomic::Ordering::Relaxed).then_some(p)
}

/// Z3's outputs for queries not asked before, solved by the pool (in order
/// asked, so the modules proved first finish first).
fn fresh_all(queries: Vec<String>) -> Vec<String> {
    let Some(p) = pool() else { return queries.iter().map(|q| fresh(q)).collect() };
    let n = queries.len();
    let (done, outs) = std::sync::mpsc::channel();
    {
        let mut jobs = p.jobs.lock().unwrap_or_else(|e| e.into_inner());
        for (i, q) in queries.into_iter().enumerate() {
            jobs.push_back((i, q, done.clone()));
        }
    }
    p.ready.notify_all();
    drop(done);
    let mut out = vec![String::new(); n];
    for (i, o) in outs.iter().take(n) {
        out[i] = o;
    }
    out
}

/// The Z3 release Checkers pins (crate `z3-src`, D46). Another release, as a
/// development build may link (`--no-default-features`), can prove less or
/// take far longer within the same work limit.
const Z3_PINNED: (u32, u32) = (5, 3);

/// Warn once if the linked Z3 is not the pinned release.
fn check_z3_version() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        let (mut major, mut minor, mut build, mut rev) = (0, 0, 0, 0);
        // SAFETY: writes four integers.
        unsafe { z3_sys::Z3_get_version(&mut major, &mut minor, &mut build, &mut rev) };
        if (major, minor) != Z3_PINNED {
            eprintln!(
                "warning: ckc is linked with Z3 {major}.{minor}.{build}, but Checkers pins Z3 {}.{}: proofs may fail or take far longer",
                Z3_PINNED.0, Z3_PINNED.1
            );
        }
    });
}

/// Evaluate one SMT-LIB script in a fresh Z3 context: Z3's output.
fn run_z3(query: &str) -> String {
    check_z3_version();
    let Ok(text) = std::ffi::CString::new(query) else { return "unknown\n(a NUL byte in the query)".into() };
    // SAFETY: the config and context are created, used and deleted on this
    // thread only; the returned string is copied before the context is deleted.
    let out = unsafe {
        let Some(cfg) = z3_sys::Z3_mk_config() else { return "unknown\n(Z3 could not start)".into() };
        let Some(ctx) = z3_sys::Z3_mk_context(cfg) else {
            z3_sys::Z3_del_config(cfg);
            return "unknown\n(Z3 could not start)".into();
        };
        z3_sys::Z3_set_error_handler(ctx, Some(ignore_error));
        let r = z3_sys::Z3_eval_smtlib2_string(ctx, text.as_ptr());
        let out = if r.is_null() { String::new() } else { std::ffi::CStr::from_ptr(r).to_string_lossy().into_owned() };
        z3_sys::Z3_del_context(ctx);
        z3_sys::Z3_del_config(cfg);
        out
    };
    out
}

/// What Z3's output says.
fn answer(out: String) -> Answer {
    if out.starts_with("unknown\n(a NUL") || out.starts_with("unknown\n(Z3 could not") {
        return Answer::Unknown(out.lines().nth(1).unwrap_or("").trim_matches(|c| c == '(' || c == ')').to_string());
    }
    // Z3 reports a rejected command as `(error …)` and carries on without it,
    // so an answer that follows an error is not about the query we meant:
    // never trust it (an `unsat` would be unsound).
    if let Some(err) = out.lines().take_while(|l| !matches!(l.trim(), "sat" | "unsat" | "unknown" | "timeout")).find(|l| l.starts_with("(error")) {
        return Answer::Unknown(format!("Z3 rejected the query (a checkers bug): {err}"));
    }
    let mut lines = out.splitn(2, '\n');
    let first = lines.next().unwrap_or("").trim().to_string();
    let rest = lines.next().unwrap_or("").to_string();
    match first.as_str() {
        "unsat" => Answer::Unsat,
        "sat" => Answer::Sat(rest),
        "unknown" | "timeout" => Answer::Unknown(first),
        other => Answer::Unknown(format!("{other} {rest}").trim().to_string()),
    }
}

/// Z3's answers to the queries: those asked before from the cache, the rest
/// solved by the pool's threads, in parallel.
fn ask_all(texts: &[Option<String>], log: &Log) -> Vec<Option<Answer>> {
    // A query asked again in the same batch waits for the first: in
    // parallel, whether its answer were reused would depend on timing.
    let mut seen = std::collections::HashSet::new();
    let again: Vec<bool> = texts.iter().map(|t| t.as_ref().is_some_and(|t| !seen.insert(t.as_str()))).collect();
    let mut results: Vec<Option<Answer>> = texts.iter().map(|_| None).collect();
    let mut asking: Vec<usize> = Vec::new();
    for (i, t) in texts.iter().enumerate() {
        let (Some(t), false) = (t, again[i]) else { continue };
        match known(t) {
            Some((out, from_disk)) => {
                log.note(t, from_disk);
                results[i] = Some(answer(out));
            }
            None => {
                log.note(t, false);
                asking.push(i);
            }
        }
    }
    let outs = fresh_all(asking.iter().filter_map(|i| texts[*i].clone()).collect());
    for (i, out) in asking.into_iter().zip(outs) {
        results[i] = Some(answer(out));
    }
    for (i, t) in texts.iter().enumerate() {
        if let (Some(t), true) = (t, again[i]) {
            results[i] = Some(ask(t, log));
        }
    }
    results
}

/// FNV-1a, for the ledger's query hashes.
fn fnv(s: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Functions recursing by `decreasing` whose recursion ends without their
/// preconditions: every termination obligation in their bodies holds with
/// the preconditions left out (D118). Recorded on the elaborator, so a
/// standard-library function decided once stays decided for its users.
fn ends_everywhere(e: &Elab, obs: &[&Obligation], log: &Log) {
    use crate::elab::ObKind;
    // Each candidate's termination obligations, without its preconditions.
    let mut cands: Vec<(crate::core::DefId, Vec<Obligation>)> = Vec::new();
    for o in obs {
        let (ObKind::Measure { .. }, Some(owner)) = (&o.kind, o.owner) else { continue };
        let Some(spec) = e.specs.get(&owner) else { continue };
        let n_pre = spec.preds.iter().filter(|p| !p.is_post).count();
        if n_pre == 0 || o.facts.len() < n_pre {
            continue;
        }
        let mut reduced = (*o).clone();
        reduced.facts.drain(..n_pre);
        match cands.iter_mut().find(|(d, _)| *d == owner) {
            Some((_, v)) => v.push(reduced),
            None => cands.push((owner, vec![reduced])),
        }
    }
    if cands.is_empty() {
        return;
    }
    let all: Vec<&Obligation> = cands.iter().flat_map(|(_, v)| v.iter()).collect();
    let user = &all[0].module;
    let defs = smt::Defs::default();
    let texts: Vec<Option<String>> =
        all.iter().map(|o| smt::Builder::new(e, user).sharing(&defs).query(o).ok().map(|q| q.text)).collect();
    let answers = ask_all(&texts, log);
    let mut k = 0;
    let mut set = e.ends_everywhere.lock().unwrap_or_else(|e| e.into_inner());
    for (d, v) in &cands {
        let ok = answers[k..k + v.len()].iter().all(|a| matches!(a, Some(Answer::Unsat)));
        k += v.len();
        if ok {
            set.insert(*d);
        }
    }
}

/// Prove the obligations of module `user` (§7.2).
pub fn verify(e: &Elab, user: &str) -> Verified {
    verify_all(e, &[user.to_string()]).pop().unwrap_or_else(Verified::empty)
}

/// Prove the obligations of each module, in order (§7.2): what each gives.
///
/// Each module's queries are made on this thread (the elaborator isn't
/// `Send`), and Z3 answers them on threads of their own while this one makes
/// the next module's: a module's slow queries no longer hold up the next
/// module's. First its branches' and candidate measures' queries, which
/// are asked at once; then its obligations'. Making them stays in order, as
/// one module after another: a module's queries depend on what the modules
/// before it found (`ends_everywhere`), and on nothing after it. Each
/// module's diagnostics are made last, from the answers.
pub fn verify_all(e: &Elab, modules: &[String]) -> Vec<Verified> {
    let mut prepared: Vec<Prepared> = Vec::new();
    let answered: Vec<(Early, Option<Solved>)> = std::thread::scope(|s| {
        let mut pending = Vec::new();
        for m in modules {
            let (mut p, early) = prepare_early(e, m);
            let early = on_thread(s, move || ask_early(early));
            prepare(e, m, &mut p);
            let solved = p.plan.take().map(|plan| on_thread(s, move || solve(plan)));
            pending.push((early, solved));
            prepared.push(p);
        }
        pending.into_iter().map(|(early, solved)| (early.join(), solved.map(Pending::join))).collect()
    });
    let mut out = Vec::new();
    for ((m, p), (early, solved)) in modules.iter().zip(prepared).zip(answered) {
        out.push(finish(e, m, p, early, solved));
    }
    out
}

/// Work given to a thread of its own, or done already if none could start.
enum Pending<'s, T> {
    Thread(std::thread::ScopedJoinHandle<'s, T>),
    Done(T),
}

impl<T> Pending<'_, T> {
    fn join(self) -> T {
        match self {
            Pending::Thread(h) => h.join().unwrap_or_else(|p| std::panic::resume_unwind(p)),
            Pending::Done(x) => x,
        }
    }
}

/// Run `f` on a thread of its own (Z3 itself runs on the pool's).
fn on_thread<'s, T, F>(s: &'s std::thread::Scope<'s, '_>, f: F) -> Pending<'s, T>
where
    T: Send + 's,
    F: FnOnce() -> T + Send + 's,
{
    fn run<T, F: FnOnce() -> T>(f: &std::sync::Mutex<Option<F>>) -> Option<T> {
        f.lock().unwrap_or_else(|e| e.into_inner()).take().map(|f| f())
    }
    let f = std::sync::Arc::new(std::sync::Mutex::new(Some(f)));
    let theirs = f.clone();
    match std::thread::Builder::new().spawn_scoped(s, move || run(&theirs).expect("run once")) {
        Ok(h) => Pending::Thread(h),
        Err(_) => Pending::Done(run(&f).expect("run once")),
    }
}

impl Verified {
    fn empty() -> Verified {
        Verified { diags: Vec::new(), ledger: Vec::new(), z3_version: None, proved: 0, asked: 0, reused: 0 }
    }
}

/// A module's queries, made: what doesn't need Z3's answers, and what is
/// needed to make its diagnostics from them.
struct Prepared<'e> {
    v: Verified,
    /// Where in the ledger the guessed measures' entries go.
    guess_at: usize,
    /// Its branches asked about (W022), and its recursive groups' candidate
    /// measures (D150).
    probes: Vec<&'e Probe>,
    guesses: Vec<Guess<'e>>,
    obs: Vec<&'e Obligation>,
    queries: Vec<Result<smt::Query, smt::Outside>>,
    /// The translated definitions its queries share, for its diagnostics'.
    defs: smt::Defs,
    /// `ends_everywhere` as its queries were made with it.
    ends: std::collections::HashSet<crate::core::DefId>,
    /// What making its queries asked Z3 (`ends_everywhere`).
    log: Log,
    /// Its obligations' queries, to solve; None if it has none to ask about.
    plan: Option<Plan>,
}

/// The texts of a module's queries about its branches and measures.
struct EarlyAsk {
    probes: Vec<Option<String>>,
    guesses: Vec<GuessAsk>,
}

/// Z3's answers about a module's branches and measures.
struct Early {
    probes: Vec<Option<Answer>>,
    guesses: Vec<Guessed>,
    log: Log,
}

/// The texts of a module's obligations' queries.
struct Plan {
    texts: Vec<Option<String>>,
    /// The weaker queries (§7.2): facts only, focused, without axioms.
    weaker: Vec<[Option<String>; 3]>,
    fallbacks: Vec<Option<String>>,
}

/// Z3's answers to a module's obligations' queries.
struct Solved {
    answers: Vec<Option<Answer>>,
    /// The query that proved each obligation, as Z3 was given it.
    proof: Vec<Option<String>>,
    log: Log,
}

/// A module's trusted and axiom entries, and the queries about its branches
/// and measures.
fn prepare_early<'e>(e: &'e Elab, user: &str) -> (Prepared<'e>, EarlyAsk) {
    let mut v = Verified::empty();
    for t in e.admits.iter().filter(|t| t.module == user) {
        v.ledger.push(LedgerEntry { span: t.span, how: "trusted", what: t.what.clone(), hash: None });
    }
    for t in e.builtin_axioms.iter().filter(|t| t.module == user) {
        v.ledger.push(LedgerEntry { span: t.span, how: "axiom", what: t.what.clone(), hash: None });
    }
    let guess_at = v.ledger.len();
    let (probes, probe_texts) = unreachable(e, user);
    let guesses = guesses(e, user);
    let ask = EarlyAsk { probes: probe_texts, guesses: guesses.iter().map(|g| g.ask.clone()).collect() };
    let p = Prepared {
        v,
        guess_at,
        probes,
        guesses,
        obs: Vec::new(),
        queries: Vec::new(),
        defs: smt::Defs::default(),
        ends: Default::default(),
        log: Log::default(),
        plan: None,
    };
    (p, ask)
}

fn ask_early(a: EarlyAsk) -> Early {
    let log = Log::default();
    let probes = if a.probes.is_empty() { Vec::new() } else { ask_all(&a.probes, &log) };
    let guesses = a.guesses.iter().map(|g| guess_ask(g, &log)).collect();
    Early { probes, guesses, log }
}

/// A module's obligations' queries.
fn prepare<'e>(e: &'e Elab, user: &str, p: &mut Prepared<'e>) {
    let v = &mut p.v;
    let obs: Vec<&Obligation> = e
        .obligations
        .iter()
        .filter(|o| o.module == user)
        .filter(|o| o.only_if_nat.as_ref().is_none_or(|t| smt::is_nat(e, t)))
        .collect();
    for (m, span, _) in e.checks.iter().filter(|c| c.0 == user) {
        let _ = m;
        let text = e.sources.get(user).and_then(|f| f.text.get(span.start as usize..span.end as usize)).unwrap_or("");
        v.ledger.push(LedgerEntry { span: *span, how: "computed", what: format!("check {}", text.trim()), hash: None });
    }
    if obs.is_empty() {
        return;
    }
    // A goal that evaluated to `True` while elaborating is proven by computation.
    let (trivial, obs): (Vec<&Obligation>, Vec<&Obligation>) = obs.into_iter().partition(|o| {
        matches!(crate::core::force(&e.g, o.goal.clone()), crate::core::Val::Con(c, _) if Some(c) == e.g.well_known.true_con)
    });
    for o in trivial {
        v.proved += 1;
        v.ledger.push(LedgerEntry { span: o.span, how: "computed", what: describe(e, o), hash: None });
    }
    if obs.is_empty() {
        return;
    }
    // Which functions recursing by `decreasing` end whatever their
    // preconditions say: their definitions need no precondition guard (M17).
    ends_everywhere(e, &obs, &p.log);
    p.ends = e.ends_everywhere.lock().unwrap_or_else(|e| e.into_inner()).clone();
    let queries: Vec<Result<smt::Query, smt::Outside>> = obs.iter().map(|o| smt::Builder::new(e, user).sharing(&p.defs).query(o)).collect();
    let texts: Vec<Option<String>> = queries.iter().map(|q| q.as_ref().ok().map(|q| q.text.clone())).collect();
    let fallbacks: Vec<Option<String>> = queries.iter().map(|q| q.as_ref().ok().and_then(|q| q.without_axioms.clone())).collect();
    let weaker: Vec<[Option<String>; 3]> = queries
        .iter()
        .map(|q| match q {
            Ok(q) => [q.facts_only.clone(), q.focused.clone(), q.without_axioms.clone()],
            Err(_) => [None, None, None],
        })
        .collect();
    if std::env::var_os("CHECKERS_SMT_DUMP").is_some() {
        for (o, t) in obs.iter().zip(&texts) {
            eprintln!(";; ── {:?} at {:?}\n{}", o.kind, o.span, t.as_deref().unwrap_or(";; outside the fragment"));
        }
    }
    p.obs = obs;
    p.queries = queries;
    p.plan = Some(Plan { texts, weaker, fallbacks });
}

/// Ask Z3 about a module's queries: needs only their texts.
fn solve(plan: Plan) -> Solved {
    let Plan { texts, weaker, fallbacks } = plan;
    let log = Log::default();
    // 1. Everything, with a small work limit (D154): most goals need little
    //    work, and this query's answer is final either way: `unsat` is a
    //    proof, `sat` a real counterexample.
    let first: Vec<Option<String>> = texts.iter().map(|t| t.as_ref().map(|t| with_limit(t, FIRST_RLIMIT))).collect();
    let mut answers: Vec<Option<Answer>> =
        ask_all(&first, &log).into_iter().map(|a| a.filter(|a| matches!(a, Answer::Unsat | Answer::Sat(_)))).collect();
    // The query that proved each obligation, as Z3 was given it.
    let mut proof: Vec<Option<String>> =
        answers.iter().zip(&first).map(|(a, t)| if matches!(a, Some(Answer::Unsat)) { t.clone() } else { None }).collect();
    // Z3 gave up: weaker queries, weakest first. `unsat` from a weaker query
    // is still a proof (§7.2).
    // 2. Definitions uninterpreted: fast when the facts in scope suffice.
    // 3. Only the definitions the goal mentions: Z3 doesn't unfold the
    //    functions whose results the facts in scope give.
    // 4. Every definition, without the quantified postconditions of other
    //    functions, which can send Z3 searching (D101).
    // Each with the small work limit, then again with a larger one where Z3
    // gave up: a query that can't prove its goal often searches until its
    // limit.
    let weaker: Vec<[Option<&String>; 3]> = weaker
        .iter()
        .zip(&answers)
        .map(|(w, a)| match a {
            None => [w[0].as_ref(), w[1].as_ref(), w[2].as_ref()],
            _ => [None, None, None],
        })
        .collect();
    // Whether each weaker query gave up with the small limit.
    let mut gave_up: Vec<[bool; 3]> = vec![[true; 3]; texts.len()];
    for limit in [FIRST_RLIMIT, QUICK_RLIMIT] {
        for tier in 0..3 {
            let ask_q: Vec<Option<String>> = weaker
                .iter()
                .enumerate()
                .map(|(k, w)| {
                    let t = w[tier]?;
                    // Asked already: proved, the same text as a weaker tier,
                    // or answered `sat` with the small limit.
                    if proof[k].is_some() || w[..tier].contains(&Some(t)) || !gave_up[k][tier] {
                        return None;
                    }
                    Some(with_limit(t, limit))
                })
                .collect();
            for (k, a) in ask_all(&ask_q, &log).into_iter().enumerate() {
                match a {
                    Some(Answer::Unsat) => proof[k] = ask_q[k].clone(),
                    Some(Answer::Sat(_)) => gave_up[k][tier] = false,
                    _ => {}
                }
            }
        }
    }
    // 5. Everything, with the full work limit: the query whose
    //    counterexample is real.
    let rest: Vec<Option<String>> = texts
        .iter()
        .enumerate()
        .map(|(k, t)| if proof[k].is_some() || answers[k].is_some() { None } else { t.clone() })
        .collect();
    for (k, a) in ask_all(&rest, &log).into_iter().enumerate() {
        if proof[k].is_some() {
            answers[k] = Some(Answer::Unsat);
        } else if a.is_some() {
            answers[k] = a;
        }
    }
    // 6. Z3 gave up on everything: a counterexample without the axioms, with
    //    the full work limit, is better than nothing (§7.2).
    let retry: Vec<Option<String>> = answers
        .iter()
        .zip(&fallbacks)
        .map(|(a, f)| if matches!(a, Some(Answer::Unknown(_))) { f.clone() } else { None })
        .collect();
    if retry.iter().any(|r| r.is_some()) {
        for (a, r) in answers.iter_mut().zip(ask_all(&retry, &log)) {
            if let Some(r @ Answer::Sat(_)) = r {
                *a = Some(r);
            }
        }
    }
    Solved { answers, proof, log }
}

/// A module's diagnostics and ledger, from Z3's answers.
fn finish(e: &Elab, user: &str, p: Prepared, early: Early, solved: Option<Solved>) -> Verified {
    let Prepared { mut v, guess_at, probes, guesses, obs, queries, defs, ends, log, .. } = p;
    // Its branches' and measures' diagnostics come first, and its guessed
    // measures' ledger entries after its trusted ones.
    let mut head = Verified::empty();
    if !probes.is_empty() {
        head.diags = unreachable_report(e, user, &probes, &early.probes);
    }
    for (g, r) in guesses.iter().zip(early.guesses) {
        guess_report(e, user, g, r, &mut head);
    }
    v.proved += head.proved;
    v.ledger.splice(guess_at..guess_at, head.ledger);
    v.diags = head.diags;
    let Some(Solved { answers, proof, log: solving }) = solved else {
        (v.asked, v.reused) = tally(&[&early.log, &log]);
        return v;
    };
    let reporting = Log::default();
    // Cases one `match` leaves out that may occur: one error (E0240).
    let mut uncovered: Vec<(Span, Vec<String>, usize)> = Vec::new();
    for (k, ((o, q), a)) in obs.iter().zip(&queries).zip(answers).enumerate() {
        if let (ObKind::Uncovered { case, .. }, false) = (&o.kind, matches!((q, &a), (Ok(_), Some(Answer::Unsat)))) {
            if let Some(u) = uncovered.iter_mut().find(|u| u.0 == o.span) {
                if !u.1.contains(case) {
                    u.1.push(case.clone());
                }
                continue;
            }
            uncovered.push((o.span, vec![case.clone()], v.diags.len()));
        }
        match (q, a) {
            (Err(why), _) => v.diags.push(outside(e, o, &why.0)),
            (Ok(q), Some(Answer::Unsat)) => {
                v.proved += 1;
                // The query that was proved, as Z3 was given it.
                let hash = Some(fnv(proof[k].as_ref().unwrap_or(&q.text)));
                v.ledger.push(LedgerEntry { span: o.span, how: "smt", what: describe(e, o), hash });
            }
            (Ok(q), Some(Answer::Sat(model))) => {
                // A model of a query without the `forall` facts may break
                // them: shown only once checked against them.
                let (shown, broken) =
                    if q.foralls { check_foralls(e, user, o, &defs, &ends, &model, &reporting) } else { (Some(model.clone()), None) };
                let shown = shown.map(|m| render_model(&m, &q.shown, &q.string_vars, &q.array_vars));
                let any = shown.is_some();
                let mut d = failed(e, o, shown);
                if let Some(n) = broken {
                    d = d.with_note(n);
                }
                if any && !q.dropped.is_empty() {
                    d = d.with_note(format!(
                        "some facts could not be given to the prover, so the counterexample may be impossible: they involve {}",
                        q.dropped.join("; ")
                    ));
                }
                v.diags.push(d);
            }
            (Ok(_), Some(Answer::Unknown(why))) => {
                let mut d = failed(e, o, None);
                d = d.with_note(format!("Z3 gave up ({why})"));
                v.diags.push(d);
            }
            (Ok(_), None) => {}
        }
    }
    for (_, cases, at) in &uncovered {
        let d = v.diags[*at].clone();
        v.diags[*at] = merge_uncovered(d, cases);
    }
    v.z3_version = z3_version();
    (v.asked, v.reused) = tally(&[&early.log, &log, &solving, &reporting]);
    v
}

/// Guess each recursive group's measure (D150): the first candidate, alone
/// and then in pairs compared lexicographically, that the prover shows every
/// recursive call makes smaller while staying a natural number. E0301 if
/// none is.
///
/// Done in three parts: the candidates' obligations are translated here
/// (`guesses`), asked about on a thread of their own (`guess_ask`), and
/// reported on (`guess_report`).
fn guesses<'e>(e: &'e Elab, user: &str) -> Vec<Guess<'e>> {
    use crate::core::{eval, quote, Lit, Prim, Tm, Val};
    use crate::elab::termination::Measure;
    let mut out = Vec::new();
    for gr in e.guess_groups.iter().filter(|g| g.module == user) {
        // Combinations to try: one measure per member.
        let mut combos: Vec<Vec<Measure>> = Vec::new();
        if gr.members.len() == 1 {
            let cs = &gr.candidates[0];
            combos.extend(cs.iter().map(|c| vec![c.clone()]));
            let firsts = &cs[..cs.len().min(6)];
            for a in firsts {
                for b in firsts {
                    if a.1 != b.1 {
                        let mut comps = a.0.clone();
                        comps.extend(b.0.iter().cloned());
                        combos.push(vec![(comps, format!("({}, {})", a.1, b.1))]);
                    }
                }
            }
        } else {
            // One candidate per member, as long as the product is small.
            let mut acc: Vec<Vec<Measure>> = vec![Vec::new()];
            for cs in &gr.candidates {
                let mut next = Vec::new();
                for a in &acc {
                    for c in cs {
                        let mut x = a.clone();
                        x.push(c.clone());
                        next.push(x);
                    }
                }
                next.truncate(64);
                acc = next;
            }
            combos = acc;
        }
        let idx = |d| gr.members.iter().position(|m| *m == d).unwrap_or(0);
        let wk = &e.g.well_known;
        let (Some(tc), Some(fc)) = (wk.true_con, wk.false_con) else { return out };
        let and = |a: Tm, b: Tm| {
            Tm::Case(
                std::rc::Rc::new(a),
                std::rc::Rc::new(crate::core::CaseTm { branches: vec![(fc, 0, Tm::ConApp(fc, vec![])), (tc, 0, b)], lits: vec![], default: None }),
            )
        };
        let or = |a: Tm, b: Tm| {
            Tm::Case(
                std::rc::Rc::new(a),
                std::rc::Rc::new(crate::core::CaseTm { branches: vec![(fc, 0, b), (tc, 0, Tm::ConApp(tc, vec![]))], lits: vec![], default: None }),
            )
        };
        // The obligation at each call, for each combination.
        let mut obs: Vec<Vec<Obligation>> = Vec::new();
        // A combination whose measure is the same expression at a call as in
        // the caller (`len src` passed `src`) can't be smaller there: not asked.
        let mut doomed: Vec<Option<Span>> = Vec::new();
        for combo in &combos {
            let mut v = Vec::new();
            let mut same_at = None;
            for c in &gr.calls {
                let (mine, theirs) = (&combo[idx(c.caller)], &combo[idx(c.callee)]);
                if mine.0.len() != theirs.0.len() {
                    continue;
                }
                let lvl = c.ob.ctx.len();
                let n_caller = e.specs.get(&c.caller).map_or(0, |s| s.n_binders);
                let here: crate::core::Env = std::rc::Rc::new((0..n_caller).map(Val::var).collect());
                let there: crate::core::Env = std::rc::Rc::new(c.args.clone());
                let a: Vec<Tm> = theirs.0.iter().map(|t| quote(&e.g, lvl, &eval(&e.g, &there, t))).collect();
                let b: Vec<Tm> = mine.0.iter().map(|t| quote(&e.g, lvl, &eval(&e.g, &here, t))).collect();
                if same_at.is_none() && c.caller == c.callee && a.iter().zip(&b).all(|(x, y)| format!("{x:?}") == format!("{y:?}")) {
                    same_at = Some(c.ob.span);
                }
                // Each part a natural number here, and the callee's below.
                let k = a.len();
                let mut lt = Tm::PrimApp(Prim::Lt, vec![a[k - 1].clone(), b[k - 1].clone()]);
                for j in (0..k - 1).rev() {
                    let less = Tm::PrimApp(Prim::Lt, vec![a[j].clone(), b[j].clone()]);
                    let same = Tm::PrimApp(Prim::Eq, vec![a[j].clone(), b[j].clone()]);
                    lt = or(less, and(same, lt));
                }
                let mut goal = lt;
                for bj in b.iter().rev() {
                    goal = and(Tm::PrimApp(Prim::Le, vec![Tm::Lit(Lit::Num(0)), bj.clone()]), goal);
                }
                let env: crate::core::Env = std::rc::Rc::new(
                    c.ob.ctx.iter().enumerate().map(|(l, x)| x.def.clone().unwrap_or_else(|| Val::var(l))).collect(),
                );
                let mut o = c.ob.clone();
                o.goal = eval(&e.g, &env, &goal);
                let func = e.g.defs[c.caller.0 as usize].name.to_string();
                o.kind = ObKind::Measure { func, measure: mine.1.clone() };
                o.text = mine.1.clone();
                v.push(o);
            }
            obs.push(v);
            doomed.push(same_at);
        }
        let defs = smt::Defs::default();
        let base: Vec<usize> = obs.iter().scan(0, |k, os| {
            let at = *k;
            *k += os.len();
            Some(at)
        }).collect();
        let texts: Vec<Option<String>> = obs
            .iter()
            .flatten()
            .map(|o| quick(smt::Builder::new(e, user).sharing(&defs).query(o).ok().map(|q| q.no_tables.unwrap_or(q.text))))
            .collect();
        let singles = combos.iter().take_while(|c| c.iter().all(|m| m.0.len() == 1)).count();
        let ask = GuessAsk { texts, base, lens: obs.iter().map(|o| o.len()).collect(), doomed: doomed.iter().map(|d| d.is_some()).collect(), singles };
        out.push(Guess { gr, combos, obs, doomed, ask });
    }
    out
}

/// A recursive group's candidate measures (D150), translated.
struct Guess<'e> {
    gr: &'e crate::elab::termination::GuessGroup,
    combos: Vec<Vec<crate::elab::termination::Measure>>,
    /// The obligation at each call, for each combination.
    obs: Vec<Vec<Obligation>>,
    /// Where a combination can't be smaller (the same at a call), if it can't.
    doomed: Vec<Option<Span>>,
    ask: GuessAsk,
}

/// What to ask Z3 about a group's candidates: needs only texts.
#[derive(Clone)]
struct GuessAsk {
    texts: Vec<Option<String>>,
    /// Each combination's first query, and how many it has.
    base: Vec<usize>,
    lens: Vec<usize>,
    doomed: Vec<bool>,
    /// How many combinations are single measures (the rest are pairs).
    singles: usize,
}

/// Z3's answers about a group's candidates, and the combination shown to
/// end, with its first query, if one was.
type Guessed = (Vec<Option<Answer>>, Option<(usize, usize)>);

/// Ask about the single measures, then the pairs, each first with a small
/// work limit (a measure that holds is usually quick to show, and one that
/// doesn't is slow to give up on), then the rest with the quick one; take
/// the first proved.
fn guess_ask(g: &GuessAsk, log: &Log) -> Guessed {
    let GuessAsk { texts, base, lens, doomed, singles } = g;
    let mut answers: Vec<Option<Answer>> = texts.iter().map(|_| None).collect();
    let small = |t: &Option<String>| {
        t.as_ref().map(|t| t.replacen(&format!("(set-option :rlimit {QUICK_RLIMIT})"), &format!("(set-option :rlimit {PROBE_RLIMIT})"), 1))
    };
    let proved = |answers: &[Option<Answer>], ci: usize| {
        lens[ci] != 0 && answers[base[ci]..base[ci] + lens[ci]].iter().all(|a| matches!(a, Some(Answer::Unsat)))
    };
    for limit in [true, false] {
        for tier in [0..*singles, *singles..lens.len()] {
            let ks: Vec<usize> = tier
                .clone()
                .filter(|ci| !doomed[*ci])
                .flat_map(|ci| base[ci]..base[ci] + lens[ci])
                .filter(|k| !matches!(answers[*k], Some(Answer::Unsat)))
                .collect();
            let asked: Vec<Option<String>> = ks.iter().map(|k| if limit { small(&texts[*k]) } else { texts[*k].clone() }).collect();
            for (k, a) in ks.iter().zip(ask_all(&asked, log)) {
                answers[*k] = a;
            }
            if let Some(ci) = tier.clone().find(|ci| proved(&answers, *ci)) {
                return (answers, Some((ci, base[ci])));
            }
        }
    }
    (answers, None)
}

/// A group's measure, from Z3's answers: its obligations in the ledger, or
/// E0301 where none was shown smaller.
fn guess_report(e: &Elab, user: &str, g: &Guess, guessed: Guessed, v: &mut Verified) {
    let Guess { gr, combos, obs, doomed, ask } = g;
    let (GuessAsk { texts, base, .. }, (answers, chosen)) = (ask, guessed);
    {
        // Each measure's calls it wasn't shown smaller at, and of those the
        // one to name: first in the group's preference (#124), the call
        // losing the parameter recursed on.
        let inside = |a: Span, b: Span| a == b || b.start <= a.start && a.end <= b.end;
        let unproved: Vec<Vec<Span>> = obs
            .iter()
            .enumerate()
            .map(|(ci, os)| {
                let ans = &answers[base[ci]..base[ci] + os.len()];
                os.iter().zip(ans).filter(|(_, a)| !matches!(a, Some(Answer::Unsat))).map(|(o, _)| o.span).collect()
            })
            .collect();
        let pick = |fails: &[Span]| {
            gr.prefer
                .iter()
                .find_map(|p| fails.iter().find(|f| inside(**f, *p) || inside(*p, **f)))
                .or(fails.first())
                .copied()
        };
        let mut tried: Vec<(String, Option<Span>)> = Vec::new();
        for (ci, fails) in unproved.iter().enumerate() {
            let failed = doomed[ci].or_else(|| pick(fails));
            tried.push((combos[ci].iter().map(|m| format!("`{}`", m.1)).collect::<Vec<_>>().join(" and "), failed));
        }
        let first_call = gr.calls.first().map(|c| c.ob.span);
        match chosen {
            Some((ci, at)) => {
                for (o, t) in obs[ci].iter().zip(&texts[at..]) {
                    v.proved += 1;
                    let mut what = describe(e, o);
                    what.push_str(" (guessed)");
                    v.ledger.push(LedgerEntry { span: o.span, how: "smt", what, hash: t.as_ref().map(|t| fnv(t)) });
                }
            }
            None => {
                // At a call no measure was shown smaller at: for the measures
                // that leave the fewest calls unproved, the one `pick` names.
                let fewest = (0..obs.len())
                    .filter(|ci| doomed[*ci].is_none() && !obs[*ci].is_empty())
                    .min_by_key(|ci| unproved[*ci].len());
                let Some(at) = fewest.and_then(|ci| pick(&unproved[ci])).or_else(|| gr.prefer.first().and_then(|p| {
                    gr.calls.iter().map(|c| c.ob.span).find(|s| inside(*s, *p) || inside(*p, *s))
                })).or(first_call)
                else {
                    return;
                };
                let names: Vec<String> = gr.members.iter().map(|d| format!("`{}`", e.g.defs[d.0 as usize].name)).collect();
                let src = e.sources.get(user);
                let line = |sp: Span| src.map(|f| f.line_col(sp.start).0).unwrap_or(0);
                let shown: Vec<String> = tried
                    .iter()
                    .take(8)
                    .map(|(m, f)| match f {
                        Some(sp) if *sp != at => format!("{m} (not shown smaller at line {})", line(*sp)),
                        _ => m.clone(),
                    })
                    .collect();
                let note = format!("measures tried, none shown smaller here: {}", shown.join(", "));
                // A lemma using itself: an induction (#76).
                let lemma = gr.members.len() == 1 && e.fn_meta.get(&gr.members[0]).is_some_and(|m| !m.is_fn);
                if lemma {
                    let name = &names[0];
                    let d = Diagnostic::error("E0301", format!("{name} uses itself, but no measure found that each use makes smaller, so this is not an induction"), at)
                        .with_label("the induction hypothesis")
                        .with_note(note)
                        .with_help(format!("use {name} only on a part of a parameter you matched on, or add `decreasing <measure>` as the first line of its proof"));
                    v.diags.push(d);
                    return;
                }
                let who = if names.len() == 1 { format!("{} terminates", names[0]) } else { format!("{} terminate", names.join(", ")) };
                let mut d = Diagnostic::error("E0301", format!("cannot show that {who}: no measure found that every recursive call makes smaller"), at)
                    .with_label("recursive call");
                d = d.with_note(note);
                v.diags.push(d.with_help("add `decreasing <measure>` as the first line of the function, or mark it `partial`"));
            }
        }
    }
}

/// W022 (D144 d): the branches of the program's own used code whose facts
/// contradict each other, by the facts alone.
///
/// Done in two parts: the branches' queries are made here, and reported on
/// (`unreachable_report`) once Z3 has answered them, on another thread.
fn unreachable<'e>(e: &'e Elab, user: &str) -> (Vec<&'e Probe>, Vec<Option<String>>) {
    if e.package_of(user) != "." {
        return (Vec::new(), Vec::new());
    }
    let inside = |a: Span, b: Span| b.start <= a.start && a.end <= b.end;
    let dead: Vec<Span> = e.dead.iter().filter(|(m, _)| m == user).map(|x| x.1).collect();
    let probes: Vec<&Probe> =
        e.probes.iter().filter(|p| p.ob.module == user && !dead.iter().any(|d| inside(p.ob.span, *d))).collect();
    if probes.is_empty() {
        return (Vec::new(), Vec::new());
    }
    let defs = smt::Defs::default();
    let texts: Vec<Option<String>> =
        probes
        .iter()
        .map(|p| {
            // Marked, so a cached answer is never taken for an obligation's.
            let q = smt::Builder::new(e, user).sharing(&defs).query(&p.ob).ok().map(|q| q.facts_only.unwrap_or(q.text));
            q.map(|t| t.replacen(&format!("(set-option :rlimit {RLIMIT})"), &format!("(set-option :rlimit {PROBE_RLIMIT})"), 1) + ";; reachable?\n")
        })
        .collect();
    (probes, texts)
}

/// W022 for the branches Z3 found never run.
fn unreachable_report(e: &Elab, user: &str, probes: &[&Probe], answers: &[Option<Answer>]) -> Vec<Diagnostic> {
    let inside = |a: Span, b: Span| b.start <= a.start && a.end <= b.end;
    // A branch reached along several paths (an arm under several cases)
    // never runs only if no path reaches it.
    let mut groups: Vec<(Span, ProbeKind, bool, &Probe)> = Vec::new();
    for (p, a) in probes.iter().zip(answers) {
        let never = matches!(a, Some(Answer::Unsat));
        match groups.iter_mut().find(|g| g.0 == p.ob.span && g.1 == p.kind) {
            Some(g) => g.2 &= never,
            None => groups.push((p.ob.span, p.kind, never, p)),
        }
    }
    let never: Vec<&(Span, ProbeKind, bool, &Probe)> = groups.iter().filter(|g| g.2).collect();
    let mut out = Vec::new();
    for g in &never {
        let (span, kind, _, p) = **g;
        // Inside a branch already reported.
        if never.iter().any(|h| !(h.0 == span && h.1 == kind) && inside(span, h.3.region) && h.3.region != p.region) {
            continue;
        }
        let both = never.iter().any(|h| h.0 == span && h.1 != kind && matches!(h.1, ProbeKind::Then | ProbeKind::Else));
        let src = e.sources.get(user).and_then(|f| f.text.get(span.start as usize..span.end as usize)).unwrap_or("").to_string();
        let mut d = match kind {
            ProbeKind::Arm => Diagnostic::warning("W022", "this arm never runs", span)
                .with_label("no value that can reach this `match` matches it")
                .with_help("remove it: a `match` needs no arm for a case that can't occur"),
            ProbeKind::Then | ProbeKind::Else if both => {
                if kind == ProbeKind::Else {
                    continue;
                }
                Diagnostic::warning("W022", "this `if` never runs", span)
                    .with_label("the facts here contradict each other")
                    .with_help("remove it")
            }
            ProbeKind::Then => Diagnostic::warning("W022", "this condition is always false", span)
                .with_label(format!("`{src}` can't be true here"))
                .with_help("remove the `if`, keeping its `else` branch"),
            ProbeKind::Else => Diagnostic::warning("W022", "this condition is always true", span)
                .with_label(format!("`{src}` can't be false here"))
                .with_help("remove the `if`, keeping its first branch"),
        };
        let mut before = p.ob.clone();
        before.facts.truncate(p.before);
        if let Some(n) = facts_note(e, &before) {
            d = d.with_note(n);
        }
        out.push(d);
    }
    out
}

fn describe(e: &Elab, o: &Obligation) -> String {
    match &o.kind {
        ObKind::Pre { callee } => format!("precondition of `{callee}`: {}", o.text),
        ObKind::Post { func, at } => {
            let src = e.sources.get(&o.module);
            let line = src.map(|f| f.line_col(at.start).0).unwrap_or(0);
            let text: String = src
                .and_then(|f| f.text.get(at.start as usize..at.end as usize))
                .unwrap_or("")
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ");
            let text = if text.chars().count() > 40 { format!("{}…", text.chars().take(40).collect::<String>()) } else { text };
            format!("postcondition of `{func}`: {} (for `{text}`, line {line})", o.text)
        }
        ObKind::Invariant { con } => format!("invariant of `{con}`: {}", o.text),
        ObKind::TypeParams { written, .. } => format!("`{written}` is a type: {}", o.text),
        ObKind::CownInvariant { alias } => format!("cown contents stay `{alias}`: {}", o.text),
        ObKind::Refined { alias, value } => format!("`{value}` is a `{alias}`: {}", o.text),
        ObKind::Weaken { sub, sup, .. } => format!("every `{sub}` is a `{sup}`: {}", o.text),
        ObKind::NatSub => format!("`Nat` subtraction `{}` stays at or above zero", o.text),
        ObKind::Measure { func, measure } => format!("termination of `{func}`: `decreasing {measure}` gets smaller"),
        ObKind::Div => format!("divisor of `{}` is not zero", o.text),
        ObKind::Index => format!("index in bounds: {}", o.text),
        ObKind::Lemma { name } => format!("lemma `{name}`: {}", o.text),
        ObKind::ClassType { name, given } => format!("every `{given}` satisfies `{name}`: {}", o.text),
        ObKind::Auto => format!("auto: {}", o.text),
        ObKind::Have => format!("have {}", o.text),
        ObKind::Uncovered { case, binding: false } => format!("`match` needs no arm for {case}: it can't occur"),
        ObKind::Uncovered { case, binding: true } => format!("the pattern needn't cover {case}: it can't occur"),
    }
}

/// The facts in scope, as Checkers source, most recent last.
fn facts_note(e: &Elab, o: &Obligation) -> Option<String> {
    let names: Vec<crate::core::Name> = o.ctx.iter().map(|l| l.name.clone()).collect();
    let lvl = o.ctx.len();
    // `x >= 0` for a `Nat` local restates its type (D121): not shown.
    let implied: Vec<String> =
        o.ctx.iter().filter(|l| crate::core::is_nat(&e.g, &l.ty)).map(|l| format!("{} >= 0", l.name)).collect();
    let mut shown: Vec<String> = implied.clone();
    for f in &o.facts {
        let s = show(&e.g, &names, &quote(&e.g, lvl, f));
        let s = match (s.strip_suffix(" == True"), s.strip_suffix(" == False")) {
            (Some(t), _) => t.to_string(),
            (_, Some(f)) if f.starts_with('(') => format!("not {f}"),
            (_, Some(f)) => format!("not ({f})"),
            _ => s,
        };
        if !shown.contains(&s) && !s.contains('$') {
            shown.push(s);
        }
    }
    let shown: Vec<String> = shown.into_iter().skip(implied.len()).collect();
    if shown.is_empty() {
        return None;
    }
    let n = shown.len();
    let tail: Vec<String> = shown.into_iter().skip(n.saturating_sub(6)).map(|s| format!("`{s}`")).collect();
    Some(format!("facts in scope{}: {}", if n > 6 { " (last 6)" } else { "" }, tail.join(", ")))
}

fn headline(o: &Obligation) -> (String, String, String) {
    match &o.kind {
        ObKind::Pre { callee } => (
            format!("cannot prove `{}`, required to call `{callee}`", o.text),
            format!("`{callee}` requires `{}`", o.text),
            "make it true before the call, e.g. with an `if` or a `match`, or strengthen this function's precondition".into(),
        ),
        ObKind::Post { func, .. } => (
            format!("cannot prove `{}`, the postcondition of `{func}`", o.text),
            "promised here".into(),
            "make the body establish it in every branch; facts about other functions come from their postconditions, or from a lemma brought in with `have`".into(),
        ),
        ObKind::Invariant { con } => (
            format!("cannot prove `{}`, required to build `{con}`", o.text),
            format!("`{con}` requires `{}`", o.text),
            "check the value before building it, e.g. with an `if`".into(),
        ),
        ObKind::TypeParams { ty, written } => (
            format!("cannot prove `{}`, required to write the type `{written}`", o.text),
            format!("`{ty}` requires `{}`", o.text),
            "give arguments for which it holds, or require it where the type is written: in the function's preconditions, or in a condition on the enclosing type's parameters".into(),
        ),
        ObKind::CownInvariant { alias } => (
            format!("cannot prove `{}`, the invariant of a cown holding `{alias}`", o.text),
            format!("the cown's new contents must be a `{alias}`"),
            format!("every behaviour on this cown must hand back a `{alias}`: check the new contents first, e.g. with an `if`"),
        ),
        ObKind::Refined { alias, value } => (
            format!("cannot prove that `{value}` is a `{alias}` (`{}`)", o.text),
            format!("this must be a `{alias}`"),
            format!("make it true first, e.g. with an `if`, or start from a value that is already a `{alias}`"),
        ),
        ObKind::Weaken { role: WeakenRole::Param, value, sub, callee, .. } => (
            format!("cannot prove that `{value}` can be called here"),
            match callee {
                Some(c) => format!("`{c}` may call this with any `{sub}`"),
                None => format!("this may be called with any `{sub}`"),
            },
            format!("pass a function that accepts every `{sub}`"),
        ),
        ObKind::Weaken { role: WeakenRole::Result, value, sub, sup, .. } => (
            format!("cannot prove that `{value}` returns a `{sup}`"),
            format!("its result is a `{sub}`, which must be a `{sup}`"),
            format!("pass a function whose result is always a `{sup}`"),
        ),
        ObKind::Weaken { role: WeakenRole::Element, value, sub, sup, .. } => (
            format!("cannot prove that every `{sub}` is a `{sup}`"),
            format!("`{value}` holds `{sub}` values where `{sup}` values are expected"),
            format!("give the values the type `{sup}` where they are built, so that each is checked there"),
        ),
        ObKind::Measure { func, measure } => (
            format!("cannot prove that `{func}` terminates: `{measure}` may not get smaller in this call"),
            format!("`decreasing {measure}` must be smaller here than on entry to `{func}`"),
            "make sure the recursive call's arguments make the measure smaller, e.g. by checking a bound first".into(),
        ),
        ObKind::NatSub => (
            "cannot prove that this `Nat` subtraction stays at or above zero".into(),
            "`-` on `Nat` needs the left side to be at least the right".into(),
            "check it first (`if a >= b then a - b else …`), or write `a + (-b)` for a signed result".into(),
        ),
        ObKind::Div => (
            "cannot prove that the divisor is not zero".into(),
            "`/` and `%` need a non-zero right side".into(),
            "check the divisor first, e.g. `if d != 0 then n / d else …`".into(),
        ),
        ObKind::Index => {
            // `o.text` is `INDEX < len ARRAY`, as written.
            let (i, a) = o.text.split_once(" < len ").unwrap_or(("i", "src"));
            let a_shown = if a.contains(' ') { format!("({a})") } else { a.to_string() };
            (
                format!("cannot prove that the index is in bounds (`{}`)", o.text),
                format!("indexing needs `{}`", o.text),
                format!("check the index first, e.g. `if {} then {a_shown}[{i}] else …`", o.text),
            )
        }
        ObKind::Lemma { name } => (
            format!("cannot prove lemma `{name}`"),
            format!("`{}`", o.text),
            "add a `proof` block: `match` on a parameter for case analysis, and `have` for facts it needs".into(),
        ),
        ObKind::ClassType { name, given } => (
            format!("cannot prove that every `{given}` satisfies `{}`, as `{name}` requires", o.text),
            format!("`{}` is `{given}` here", name.rsplit('.').next().unwrap_or(name)),
            format!("give `{}` a type whose values all satisfy it", name.rsplit('.').next().unwrap_or(name)),
        ),
        ObKind::Auto => (
            format!("`auto` cannot prove `{}`", o.text),
            "the goal here".into(),
            "split into cases with `match`, or add facts with `have`".into(),
        ),
        ObKind::Have => (
            format!("cannot prove `have {}`", o.text),
            "asserted here".into(),
            "prove it with a lemma, or add the facts it needs first".into(),
        ),
        ObKind::Uncovered { case, binding } => (
            format!("this {} does not cover {case}", if *binding { "pattern" } else { "`match`" }),
            "not exhaustive".into(),
            if *binding { crate::elab::BINDING_HELP.to_string() } else { uncovered_help(std::slice::from_ref(case)) },
        ),
    }
}

/// What to do about cases a `match` leaves out that may occur.
fn uncovered_help(cases: &[String]) -> String {
    match cases {
        [one] if one.starts_with('`') && !one.contains(" when ") && !one.contains(" for ") => {
            format!("add an arm `{} -> …`, or a catch-all `_ -> …`", one.trim_matches('`'))
        }
        [_] => "add an arm for it, or a catch-all `_ -> …`".to_string(),
        _ => "add arms for these, or a catch-all `_ -> …`".to_string(),
    }
}

/// The cases left out of one `match` that may occur, as one error (E0240):
/// the first's diagnostic, its message and help naming them all.
fn merge_uncovered(mut d: Diagnostic, cases: &[String]) -> Diagnostic {
    if cases.len() > 1 {
        let n = cases.len();
        let list = match n {
            2 => format!("{} or {}", cases[0], cases[1]),
            3 => format!("{}, {} or {}", cases[0], cases[1], cases[2]),
            _ => format!("{}, {}, {} and {} more", cases[0], cases[1], cases[2], n - 3),
        };
        if d.message.starts_with("this pattern") {
            d.message = format!("this pattern does not cover {list}");
        } else {
            d.message = format!("this `match` does not cover {list}");
            d.help = Some(uncovered_help(cases));
        }
    }
    d
}

fn failed(e: &Elab, o: &Obligation, model: Option<String>) -> Diagnostic {
    let (msg, label, help) = headline(o);
    let code = if matches!(o.kind, ObKind::Uncovered { .. }) { "E0240" } else { "E0450" };
    let mut d = Diagnostic::error(code, msg, o.span).with_label(label);
    if let ObKind::Weaken { .. } = &o.kind {
        d = d.with_note(format!("it needs `{}`", o.text));
    }
    if let ObKind::Post { at, .. } = &o.kind {
        if let Some(f) = e.sources.get(&o.module) {
            let (line, _) = f.line_col(at.start);
            let text: String = f.text.get(at.start as usize..at.end as usize).unwrap_or("").split_whitespace().collect::<Vec<_>>().join(" ");
            d = d.with_note(format!("for the value returned on line {line}: `{text}`"));
        }
    }
    // A case left out: the facts are the case itself.
    if let Some(n) = facts_note(e, o).filter(|_| !matches!(o.kind, ObKind::Uncovered { .. })) {
        d = d.with_note(n);
    }
    // Sealed functions from other modules (D54) are only known by their contracts.
    let mut sealed = Vec::new();
    let lvl = o.ctx.len();
    crate::elab::collect_sealed(&quote(&e.g, lvl, &o.goal), &e.g, &o.module, &mut sealed);
    let sealed_note = sealed.first().map(|d| {
        let info = &e.g.defs[d.0 as usize];
        // A builtin has no body for the prover to see, wherever it is used.
        let what = if info.body.is_none() { format!("is built into `{}`", info.module) } else { format!("is sealed in `{}`", info.module) };
        format!("`{}` {what}: here the prover knows only its postconditions and the lemmas you bring in with `have`", info.name)
    });
    match model.filter(|m| !m.is_empty()) {
        Some(m) if sealed_note.is_none() => d = d.with_note(format!("counterexample: {m}")),
        _ => {}
    }
    if let Some(n) = sealed_note {
        d = d.with_note(n);
    }
    d.with_help(help)
}

fn outside(e: &Elab, o: &Obligation, why: &str) -> Diagnostic {
    let (msg, label, _) = headline(o);
    let code = if matches!(o.kind, ObKind::Uncovered { .. }) { "E0240" } else { "E0451" };
    let mut d = Diagnostic::error(code, msg, o.span)
        .with_label(label)
        .with_note(format!("this obligation is outside what the prover handles: it involves {why}"));
    if let Some(n) = facts_note(e, o) {
        d = d.with_note(n);
    }
    d.with_help("state the fact you need as a lemma and bring it in with `have`")
}

/// Check Z3's counterexample against the `forall` facts in scope, which its
/// query left out (D137): the same query with them given to Z3, quantified,
/// first with the model's values fixed, then free. A model of that query is
/// a counterexample; without one, the note saying why none is shown.
fn check_foralls(
    e: &Elab,
    user: &str,
    o: &Obligation,
    defs: &smt::Defs,
    ends: &std::collections::HashSet<crate::core::DefId>,
    model: &str,
    log: &Log,
) -> (Option<String>, Option<String>) {
    let why = |broken: bool| {
        Some(format!(
            "no counterexample: the one Z3 found {} a `forall` in scope, which the prover uses only by name, with `have`",
            if broken { "breaks" } else { "could not be checked against" }
        ))
    };
    let Ok(q) = smt::Builder::new(e, user).sharing(defs).ending(ends).with_foralls().query(o) else { return (None, why(false)) };
    let text = with_limit(&q.text, QUICK_RLIMIT);
    let Some(at) = text.rfind("(check-sat)") else { return (None, why(false)) };
    let mut pins = String::new();
    if let Some(Sx::List(pairs)) = parse_sx(model).first() {
        for p in pairs {
            if let Sx::List(kv) = p {
                if let (Some(Sx::Atom(k)), Some(v)) = (kv.first(), kv.get(1)) {
                    let v = print_sx(v);
                    // Values of abstract sorts (`a#0!val!0`) and Z3's own
                    // functions (`k!0`) can't be written in a query.
                    if !v.contains('!') {
                        pins += &format!("(assert (= {k} {v}))\n");
                    }
                }
            }
        }
    }
    let pinned = format!("{}{pins}{}", &text[..at], &text[at..]);
    let broken = match ask(&pinned, log) {
        Answer::Sat(m) => return (Some(m), None),
        Answer::Unsat => true,
        Answer::Unknown(_) => false,
    };
    match ask(&text, log) {
        Answer::Sat(m) => (Some(m), None),
        _ => (None, why(broken)),
    }
}

fn print_sx(x: &Sx) -> String {
    match x {
        Sx::Atom(a) => a.clone(),
        Sx::List(items) => format!("({})", items.iter().map(print_sx).collect::<Vec<_>>().join(" ")),
    }
}

/// Accumulate entries for `checkers trust`.
pub fn ledger_text(file: &crate::source::SourceFile, v: &Verified) -> String {
    let mut out = String::new();
    let mut entries = v.ledger.clone();
    entries.sort_by_key(|x| (x.span.start, x.how));
    for x in &entries {
        let (line, col) = file.line_col(x.span.start);
        let hash = x.hash.map(|h| format!("  [{h:016x}]")).unwrap_or_default();
        out += &format!("{}:{line}:{col}  {:<8} {}{hash}\n", file.name, x.how, x.what);
    }
    if let Some(z) = &v.z3_version {
        out += &format!("solver: {z}\n");
    }
    out
}

/// A dependency's part of the trust ledger (D109): what it trusts, line by
/// line, then one line for what was proved or computed.
pub fn ledger_summary(file: &crate::source::SourceFile, v: &Verified) -> String {
    let mut out = String::new();
    let mut entries: Vec<&LedgerEntry> = v.ledger.iter().filter(|x| x.how == "trusted" || x.how == "axiom").collect();
    entries.sort_by_key(|x| (x.span.start, x.how));
    for x in &entries {
        let (line, col) = file.line_col(x.span.start);
        out += &format!("{}:{line}:{col}  {:<8} {}\n", file.name, x.how, x.what);
    }
    let smt = v.ledger.iter().filter(|x| x.how == "smt").count();
    let computed = v.ledger.iter().filter(|x| x.how == "computed").count();
    if smt + computed > 0 {
        out += &format!("{}  proved   {smt} by smt, {computed} computed\n", file.name);
    }
    if let Some(z) = &v.z3_version {
        out += &format!("solver: {z}\n");
    }
    out
}

// ── counterexamples ─────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

fn parse_sx(s: &str) -> Vec<Sx> {
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while i < chars.len() {
        if let Some(x) = parse_one(&chars, &mut i) {
            out.push(x);
        } else {
            break;
        }
    }
    out
}

fn parse_one(c: &[char], i: &mut usize) -> Option<Sx> {
    while *i < c.len() && c[*i].is_whitespace() {
        *i += 1;
    }
    if *i >= c.len() {
        return None;
    }
    match c[*i] {
        '(' => {
            *i += 1;
            let mut items = Vec::new();
            loop {
                while *i < c.len() && c[*i].is_whitespace() {
                    *i += 1;
                }
                if *i >= c.len() {
                    return Some(Sx::List(items));
                }
                if c[*i] == ')' {
                    *i += 1;
                    return Some(Sx::List(items));
                }
                items.push(parse_one(c, i)?);
            }
        }
        ')' => {
            *i += 1;
            None
        }
        '|' => {
            let start = *i;
            *i += 1;
            while *i < c.len() && c[*i] != '|' {
                *i += 1;
            }
            *i += 1;
            Some(Sx::Atom(c[start..(*i).min(c.len())].iter().collect()))
        }
        '"' => {
            let start = *i;
            *i += 1;
            while *i < c.len() {
                if c[*i] == '"' {
                    if c.get(*i + 1) == Some(&'"') {
                        *i += 2;
                        continue;
                    }
                    break;
                }
                *i += 1;
            }
            *i += 1;
            Some(Sx::Atom(c[start..(*i).min(c.len())].iter().collect()))
        }
        _ => {
            let start = *i;
            while *i < c.len() && !c[*i].is_whitespace() && c[*i] != '(' && c[*i] != ')' {
                *i += 1;
            }
            Some(Sx::Atom(c[start..*i].iter().collect()))
        }
    }
}

/// `|prelude.Cons|` → `Cons`.
fn short(a: &str) -> String {
    let a = a.trim_matches('|');
    a.rsplit('.').next().unwrap_or(a).to_string()
}

fn pretty(x: &Sx) -> String {
    // A byte sequence: a `String` (its UTF-8 bytes, §7.3) or `Bytes`.
    if let Some(b) = seq_bytes(x) {
        return match std::str::from_utf8(&b) {
            Ok(t) => format!("{t:?}"),
            Err(_) => checkers_rt::ops::show_bytes(&b),
        };
    }
    if let Sx::List(l) = x {
        if matches!(l.first(), Some(Sx::Atom(h)) if h == "seq.unit" || h == "seq.++") {
            return "…".into();
        }
    }
    match x {
        Sx::Atom(a) => match a.as_str() {
            "true" => "True".into(),
            "false" => "False".into(),
            a if a.starts_with('"') => a.replace("\"\"", "\\\""),
            a if short(a) == "Nil" => "[]".into(),
            // A datatype's stand-in base constructor (`smt::base_sym`): no
            // value a program can build.
            a if a.trim_matches('|').ends_with("#base") => "…".into(),
            a => short(a),
        },
        Sx::List(items) => {
            let head = match items.first() {
                Some(Sx::Atom(h)) => h.as_str(),
                Some(Sx::List(l)) if matches!(l.first(), Some(Sx::Atom(a)) if a == "as") => {
                    if let Some(Sx::Atom(c)) = l.get(1) {
                        return pretty_con(&short(c), &items[1..]);
                    }
                    ""
                }
                _ => "",
            };
            match head {
                "-" if items.len() == 2 => format!("-{}", pretty(&items[1])),
                "as" => match items.get(1) {
                    Some(Sx::Atom(c)) => pretty_con(&short(c), &[]),
                    _ => "?".into(),
                },
                h if h.starts_with("|tuple") => {
                    format!("({})", items[1..].iter().map(pretty).collect::<Vec<_>>().join(", "))
                }
                "" => "?".into(),
                h => pretty_con(&short(h), &items[1..]),
            }
        }
    }
}

fn pretty_con(c: &str, args: &[Sx]) -> String {
    // A datatype's stand-in base constructor (`smt::base_sym`), or a
    // function giving only it (from an empty type): no value to show.
    if c.ends_with("#base") || c == "const" && args.len() == 1 && pretty(&args[0]) == "…" {
        return "…".into();
    }
    if c == "Nil" && args.is_empty() {
        return "[]".into();
    }
    if c == "Cons" && args.len() == 2 {
        let mut items = vec![pretty(&args[0])];
        let mut rest = args[1].clone();
        loop {
            match &rest {
                Sx::List(l) if l.len() == 3 && matches!(&l[0], Sx::Atom(a) if short(a) == "Cons")
                    || l.len() == 3 && matches!(&l[0], Sx::List(x) if matches!(x.get(1), Some(Sx::Atom(a)) if short(a) == "Cons")) =>
                {
                    items.push(pretty(&l[1]));
                    rest = l[2].clone();
                }
                other => {
                    let tail = pretty(other);
                    if tail != "[]" {
                        return format!("{} :: {tail}", items.join(" :: "));
                    }
                    break;
                }
            }
        }
        // A long list: its start and its length are what matter.
        if items.len() > 8 {
            let n = items.len();
            items.truncate(3);
            return format!("[{}, … ({n} items)]", items.join(", "));
        }
        return format!("[{}]", items.join(", "));
    }
    if args.is_empty() {
        return c.to_string();
    }
    let parts: Vec<String> = args
        .iter()
        .map(|a| {
            let p = pretty(a);
            if p.contains(' ') && !p.starts_with('[') && !p.starts_with('(') {
                format!("({p})")
            } else {
                p
            }
        })
        .collect();
    format!("{c} {}", parts.join(" "))
}

/// Substitute Z3's `(let ((x v) …) body)` in a model value.
fn unlet(x: &Sx, env: &[(String, Sx)]) -> Sx {
    match x {
        Sx::Atom(a) => env.iter().rev().find(|(n, _)| n == a).map(|(_, v)| v.clone()).unwrap_or_else(|| x.clone()),
        Sx::List(items) => {
            if let (Some(Sx::Atom(h)), Some(Sx::List(binds)), Some(body)) = (items.first(), items.get(1), items.get(2)) {
                if h == "let" {
                    let mut env2 = env.to_vec();
                    for b in binds {
                        if let Sx::List(kv) = b {
                            if let (Some(Sx::Atom(n)), Some(v)) = (kv.first(), kv.get(1)) {
                                let v = unlet(v, &env2);
                                env2.push((n.clone(), v));
                            }
                        }
                    }
                    return unlet(body, &env2);
                }
            }
            Sx::List(items.iter().map(|i| unlet(i, env)).collect())
        }
    }
}

/// Bytes in a model: `(seq.++ (seq.unit 104) …)` → `b"h…"`.
fn seq_bytes(x: &Sx) -> Option<Vec<u8>> {
    match x {
        Sx::List(l) => match l.first() {
            Some(Sx::Atom(h)) if h == "seq.unit" => match l.get(1) {
                Some(Sx::Atom(n)) => n.parse::<u8>().ok().map(|b| vec![b]),
                _ => None,
            },
            Some(Sx::Atom(h)) if h == "seq.++" => {
                let mut v = Vec::new();
                for p in &l[1..] {
                    v.extend(seq_bytes(p)?);
                }
                Some(v)
            }
            Some(Sx::Atom(h)) if h == "as" => matches!(l.get(1), Some(Sx::Atom(a)) if a == "seq.empty").then(Vec::new),
            _ => None,
        },
        Sx::Atom(a) if a == "seq.empty" => Some(Vec::new()),
        _ => None,
    }
}

/// The elements of a sequence in a model.
fn seq_items(x: &Sx) -> Option<Vec<Sx>> {
    match x {
        Sx::List(l) => match l.first() {
            Some(Sx::Atom(h)) if h == "seq.unit" => l.get(1).map(|e| vec![e.clone()]),
            Some(Sx::Atom(h)) if h == "seq.++" => {
                let mut v = Vec::new();
                for p in &l[1..] {
                    v.extend(seq_items(p)?);
                }
                Some(v)
            }
            Some(Sx::Atom(h)) if h == "as" => matches!(l.get(1), Some(Sx::Atom(a)) if a == "seq.empty").then(Vec::new),
            _ => None,
        },
        Sx::Atom(a) if a == "seq.empty" => Some(Vec::new()),
        _ => None,
    }
}

fn render_model(text: &str, shown: &[(String, String)], strings: &[String], arrays: &[String]) -> String {
    let sx = parse_sx(text);
    let Some(Sx::List(pairs)) = sx.first() else { return String::new() };
    let mut found: Vec<(usize, String)> = Vec::new();
    for p in pairs {
        if let Sx::List(kv) = p {
            if let (Some(Sx::Atom(k)), Some(v)) = (kv.first(), kv.get(1)) {
                if let Some(pos) = shown.iter().position(|(n, _)| n == k) {
                    let v = unlet(v, &[]);
                    let items = if arrays.contains(k) { seq_items(&v) } else { None };
                    let s = match seq_bytes(&v) {
                        // An array of anything but `U8` (D133).
                        _ if items.is_some() => {
                            let shown: Vec<String> = items.unwrap_or_default().iter().map(pretty).collect();
                            format!("array.from_list [{}]", shown.join(", "))
                        }
                        // A `String` is its UTF-8 bytes to the solver (§7.3).
                        Some(b) if strings.contains(k) => match String::from_utf8(b.clone()) {
                            Ok(t) => format!("{t:?}"),
                            Err(_) => checkers_rt::ops::show_bytes(&b),
                        },
                        Some(b) => checkers_rt::ops::show_bytes(&b),
                        None => pretty(&v),
                    };
                    // Values of abstract types (capabilities, type variables) say nothing useful.
                    if !s.contains('!') && !s.contains('?') {
                        let lvl: usize = k.trim_matches('|').rsplit('#').next().and_then(|n| n.parse().ok()).unwrap_or(pos);
                        found.push((lvl, format!("{} = {s}", shown[pos].1)));
                    }
                }
            }
        }
    }
    found.sort();
    found.into_iter().map(|x| x.1).collect::<Vec<_>>().join(", ")
}
