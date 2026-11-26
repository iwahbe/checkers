//! The prover pipeline (SPEC §7, M3): obligations → SMT-LIB → Z3 → diagnostics
//! and the trust ledger.

pub mod smt;

use crate::core::quote;
use crate::diag::Diagnostic;
use crate::elab::{Elab, ObKind, Obligation, Probe, ProbeKind, Vacuity, VacuityKind, WeakenRole};
use crate::source::Span;

/// One entry of the trust ledger (§7.4).
#[derive(Clone, Debug)]
pub struct LedgerEntry {
    pub span: Span,
    pub how: &'static str,
    pub what: String,
}

#[derive(Clone)]
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

/// For asking whether a declaration's conditions can all hold (E0457): 2.8
/// times the most any answer needs in the repository (7 180, a `sat`, of
/// 3 528 queries, 25/11/2026); a contradiction among a few conditions
/// needs far less (under 200). One query per declaration, so a query Z3
/// gives up on (77 of them, reported as nothing) mustn't cost much.
pub const VACUITY_RLIMIT: u64 = 20_000;

/// The work limit each query is tried with first (D154): nearly every
/// answer in the repository needs far less (all but 0.2%), and a query that
/// can't prove its goal often searches until its limit, so giving up costs
/// this before the next query.
pub const FIRST_RLIMIT: u64 = 200_000;

/// A weaker query, tried first: with the smaller work limit.
fn quick(q: Option<String>) -> Option<String> {
    q.map(|t| with_limit(&t, QUICK_RLIMIT))
}

/// The option that sets a query's work limit: Z3 keeps this one in the
/// query's own context. `:rlimit` and `:timeout` are parameters of the whole
/// process, which every context copies when any is set: a query would run
/// with the limit of one solved at the same time on another thread.
const LIMIT_OPTION: &str = "(set-option :reproducible-resource-limit ";

fn limit_option(limit: u64) -> String {
    format!("{LIMIT_OPTION}{limit})")
}

/// The options every query starts with: the safety cap, the same for all,
/// then its work limit (setting the cap copies the process's limit, none).
pub(crate) fn options(limit: u64) -> String {
    format!("(set-option :produce-models true)\n(set-option :timeout {SAFETY_MS})\n{}\n", limit_option(limit))
}

/// A query made with the work limit `from`, with the limit `to`.
fn relimit(t: &str, from: u64, to: u64) -> String {
    t.replacen(&limit_option(from), &limit_option(to), 1)
}

/// A query with another work limit.
fn with_limit(t: &str, limit: u64) -> String {
    relimit(t, RLIMIT, limit)
}

/// A wall-clock cap, in case Z3 is slow to use up its work limit. An answer
/// it cuts off depends on the machine, so it isn't cached.
pub const SAFETY_MS: u64 = 60_000;

/// Where Z3's answers are cached (D100), if anywhere.
static CACHE: std::sync::Mutex<Option<std::path::PathBuf>> = std::sync::Mutex::new(None);
static ASKED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static REUSED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

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

const MODULE_HEADER: &str = "checkers module 3";

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
        let mut parts = l.splitn(4, ' ');
        let start: u32 = parts.next()?.parse().ok()?;
        let end: u32 = parts.next()?.parse().ok()?;
        let how = match parts.next()? {
            "trusted" => "trusted",
            "axiom" => "axiom",
            "computed" => "computed",
            "smt" => "smt",
            _ => return None,
        };
        let what = parts.next()?.replace("\\n", "\n");
        ledger.push(LedgerEntry { span: Span { start, end }, how, what });
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
        out += &format!("{} {} {} {}\n", x.span.start, x.span.end, x.how, x.what.replace('\n', "\\n"));
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
fn ask(query: &str) -> Answer {
    answer(ask_out(query))
}

/// Z3's output for one SMT-LIB script, from the cache or a fresh Z3 context.
fn ask_out(query: &str) -> String {
    ASKED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    // The same query asked twice in this process: Z3's answer depends only
    // on the text, so it is reused (D154).
    static MEMO: std::sync::Mutex<Option<std::collections::HashMap<String, String>>> = std::sync::Mutex::new(None);
    let memo = |out: &str| {
        MEMO.lock().unwrap_or_else(|e| e.into_inner()).get_or_insert_with(Default::default).insert(query.to_string(), out.to_string());
    };
    if let Some(out) = MEMO.lock().unwrap_or_else(|e| e.into_inner()).as_ref().and_then(|m| m.get(query)).cloned() {
        REUSED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return out;
    }
    let out = match cached(query) {
        Some(out) => {
            REUSED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            out
        }
        None => {
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
                let what = if query.starts_with("(set-option :produce-unsat-cores") { "(can the conditions hold?)".to_string() } else { query.lines().find(|l| l.starts_with("(assert (not")).unwrap_or("").chars().take(120).collect::<String>() };
                let said = out.split_whitespace().next().unwrap_or("?");
                let limit = query.split(LIMIT_OPTION).nth(1).and_then(|r| r.split(')').next()).unwrap_or("?");
                eprintln!("smt {:>6} ms {:>7} bytes {said:>7} rlimit {limit:>8} used {used:>8} {what}", start.elapsed().as_millis(), query.len());
                if let Some(err) = out.lines().find(|l| l.starts_with("(error")) {
                    eprintln!("smt error {err}");
                }
            }
            let cut_off = out.starts_with("unknown") && start.elapsed().as_millis() as u64 >= SAFETY_MS * 9 / 10;
            if !cut_off {
                store(query, &out);
                memo(&out);
            }
            out
        }
    };
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

/// Solve the queries on a few worker threads (each Z3 context is heavy).
fn ask_all(texts: &[Option<String>]) -> Vec<Option<Answer>> {
    ask_all_out(texts).into_iter().map(|o| o.map(answer)).collect()
}

/// `ask_all`, with each query handed to the workers as `produce` makes it,
/// so they solve while the next is made (on this thread: the elaborator
/// isn't `Send`). Answers depend only on the queries' texts, as in
/// `ask_all_out`: a text asked again waits for the first.
fn ask_produced(n: usize, mut produce: impl FnMut(usize) -> Option<String>) -> Vec<Option<Answer>> {
    let workers = std::thread::available_parallelism().map_or(2, |n| n.get()).min(8);
    let results: Vec<std::sync::Mutex<Option<String>>> = (0..n).map(|_| std::sync::Mutex::new(None)).collect();
    // The queries made so far, and whether all are.
    let queue: std::sync::Mutex<(std::collections::VecDeque<(usize, String)>, bool)> = std::sync::Mutex::new((Default::default(), false));
    let ready = std::sync::Condvar::new();
    let mut again: Vec<(usize, String)> = Vec::new();
    std::thread::scope(|s| {
        for _ in 0..workers {
            // Z3 recurses deeply on large terms: give it a big stack.
            let worker = std::thread::Builder::new().stack_size(512 << 20);
            let spawned = worker.spawn_scoped(s, || loop {
                let next = {
                    let mut q = queue.lock().unwrap_or_else(|e| e.into_inner());
                    loop {
                        if let Some(job) = q.0.pop_front() {
                            break Some(job);
                        }
                        if q.1 {
                            break None;
                        }
                        q = ready.wait(q).unwrap_or_else(|e| e.into_inner());
                    }
                };
                let Some((i, t)) = next else { break };
                let a = ask_out(&t);
                *results[i].lock().unwrap_or_else(|e| e.into_inner()) = Some(a);
            });
            if spawned.is_err() {
                break;
            }
        }
        let mut seen = std::collections::HashSet::new();
        for i in 0..n {
            let Some(t) = produce(i) else { continue };
            if !seen.insert(t.clone()) {
                again.push((i, t));
                continue;
            }
            queue.lock().unwrap_or_else(|e| e.into_inner()).0.push_back((i, t));
            ready.notify_one();
        }
        queue.lock().unwrap_or_else(|e| e.into_inner()).1 = true;
        ready.notify_all();
    });
    for (i, t) in again {
        *results[i].lock().unwrap_or_else(|e| e.into_inner()) = Some(ask_out(&t));
    }
    results.into_iter().map(|m| m.into_inner().unwrap_or_else(|e| e.into_inner()).map(answer)).collect()
}

/// Z3's output for each query, solved on a few worker threads.
fn ask_all_out(texts: &[Option<String>]) -> Vec<Option<String>> {
    let workers = std::thread::available_parallelism().map_or(2, |n| n.get()).min(8);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let results: Vec<std::sync::Mutex<Option<String>>> = texts.iter().map(|_| std::sync::Mutex::new(None)).collect();
    // A query asked again in the same batch waits for the first: in
    // parallel, whether its answer were reused would depend on timing.
    let mut seen = std::collections::HashSet::new();
    let again: Vec<bool> = texts.iter().map(|t| t.as_ref().is_some_and(|t| !seen.insert(t.as_str()))).collect();
    std::thread::scope(|s| {
        for _ in 0..workers {
            // Z3 recurses deeply on large terms: give it a big stack.
            let worker = std::thread::Builder::new().stack_size(512 << 20);
            let spawned = worker.spawn_scoped(s, || loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(t) = texts.get(i) else { break };
                if let (Some(t), false) = (t, again[i]) {
                    let a = ask_out(t);
                    *results[i].lock().unwrap_or_else(|e| e.into_inner()) = Some(a);
                }
            });
            if spawned.is_err() {
                break;
            }
        }
    });
    for (i, t) in texts.iter().enumerate() {
        if let (Some(t), true) = (t, again[i]) {
            *results[i].lock().unwrap_or_else(|e| e.into_inner()) = Some(ask_out(t));
        }
    }
    results.into_iter().map(|m| m.into_inner().unwrap_or_else(|e| e.into_inner())).collect()
}

/// FNV-1a, for the names of cached answers.
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
fn ends_everywhere(e: &Elab, obs: &[&Obligation]) {
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
    let answers = ask_all(&texts);
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
/// Module `user`'s proofs phase: its proofs (`proved`), after W022 for
/// its branches that never run, which needs the program's unused code.
pub fn proofs(e: &Elab, user: &str) -> Verified {
    let mut v = proved(e, user);
    let (asked0, reused0) = (ASKED.load(std::sync::atomic::Ordering::Relaxed), REUSED.load(std::sync::atomic::Ordering::Relaxed));
    let mut diags = unreachable(e, user);
    v.asked += ASKED.load(std::sync::atomic::Ordering::Relaxed) - asked0;
    v.reused += REUSED.load(std::sync::atomic::Ordering::Relaxed) - reused0;
    diags.append(&mut v.diags);
    v.diags = diags;
    v
}

/// Module `user`'s obligations proved: the first time, by `verify`; after
/// that, as they were. A module is proved once per program, whether
/// first for a value known at compile time (§8.9) or in the proofs phase.
pub fn proved(e: &Elab, user: &str) -> Verified {
    if let Some(v) = e.module_proofs.borrow().get(user) {
        return v.clone();
    }
    e.proving.borrow_mut().insert(user.to_string());
    let v = verify(e, user);
    e.proving.borrow_mut().remove(user);
    e.module_proofs.borrow_mut().insert(user.to_string(), v.clone());
    v
}

fn verify(e: &Elab, user: &str) -> Verified {
    // Those proved already, so that the module's own functions could run
    // while it was checked (§8.9): taken as proved.
    let early = e.early.borrow();
    let obs: Vec<&Obligation> = e
        .obligations
        .iter()
        .enumerate()
        .filter(|(k, o)| o.module == user && !early.proved(*k, o))
        .map(|(_, o)| o)
        .filter(|o| o.only_if_nat.as_ref().is_none_or(|t| smt::is_nat(e, t)))
        .collect();
    let mut v = Verified { diags: Vec::new(), ledger: Vec::new(), z3_version: None, proved: 0, asked: 0, reused: 0 };
    v.proved += early.counts.get(user).copied().unwrap_or(0);
    v.ledger.extend(early.ledger.iter().filter(|(m, _)| m == user).map(|(_, l)| l.clone()));
    drop(early);
    let (asked0, reused0) = (ASKED.load(std::sync::atomic::Ordering::Relaxed), REUSED.load(std::sync::atomic::Ordering::Relaxed));
    for t in e.admits.iter().filter(|t| t.module == user) {
        v.ledger.push(LedgerEntry { span: t.span, how: "trusted", what: t.what.clone() });
    }
    for t in e.builtin_axioms.iter().filter(|t| t.module == user) {
        v.ledger.push(LedgerEntry { span: t.span, how: "axiom", what: t.what.clone() });
    }
    v.diags.extend(vacuous(e, user));
    guess_measures(e, user, &mut v);
    for (m, span, _) in e.checks.iter().filter(|c| c.0 == user) {
        let _ = m;
        let text = e.sources.get(user).and_then(|f| f.text.get(span.start as usize..span.end as usize)).unwrap_or("");
        v.ledger.push(LedgerEntry { span: *span, how: "computed", what: format!("check {}", text.trim()) });
    }
    if obs.is_empty() {
        return v;
    }
    // A goal that evaluated to `True` while elaborating is proven by computation.
    let (trivial, obs): (Vec<&Obligation>, Vec<&Obligation>) = obs.into_iter().partition(|o| {
        matches!(crate::core::force(&e.g, o.goal.clone()), crate::core::Val::Con(c, _) if Some(c) == e.g.well_known.true_con)
    });
    for o in trivial {
        v.proved += 1;
        v.ledger.push(LedgerEntry { span: o.span, how: "computed", what: describe(e, o) });
    }
    if obs.is_empty() {
        return v;
    }
    let with_values = with_known_values(e, &obs, &mut v.ledger);
    let obs: Vec<&Obligation> = with_values.iter().collect();
    let (defs, queries, answers, _) = solve(e, user, &obs);
    // Cases one `match` leaves out that may occur: one error (E0240).
    let mut uncovered: Vec<(Span, Vec<String>, usize)> = Vec::new();
    // A call whose result isn't shown to be of its type (E0456, or at a
    // known instance requiring less): a postcondition failing for the
    // same value returned is the same error, reported once.
    let mut bad_calls: Vec<Span> = Vec::new();
    let mut post_fails: Vec<(usize, Span)> = Vec::new();
    // A postcondition outside what the prover handles is so for each value
    // returned: one error, listing them (its diagnostic, the obligations).
    let mut outside_posts: Vec<(usize, Vec<usize>)> = Vec::new();
    for (k, ((o, q), a)) in obs.iter().zip(&queries).zip(answers).enumerate() {
        if let (Err(why), ObKind::Post { .. }) = (q, &o.kind) {
            let same = |j: usize| {
                let p = obs[j];
                p.span == o.span && p.module == o.module && p.text == o.text && matches!(&queries[j], Err(w) if w.0 == why.0)
            };
            if let Some(g) = outside_posts.iter_mut().find(|g| same(g.1[0])) {
                g.1.push(k);
                continue;
            }
            outside_posts.push((v.diags.len(), vec![k]));
        }
        if !matches!((q, &a), (Ok(_), Some(Answer::Unsat)) | (Ok(_), None)) {
            match &o.kind {
                ObKind::AtAlias { call: Some(_), .. } | ObKind::KnownResult { .. } => bad_calls.push(o.span),
                ObKind::Post { at, .. } => post_fails.push((v.diags.len(), *at)),
                _ => {}
            }
        }
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
            (Err(why), _) => v.diags.push(outside(e, &[o], &why.0)),
            (Ok(_), Some(Answer::Unsat)) => {
                v.proved += 1;
                v.ledger.push(LedgerEntry { span: o.span, how: "smt", what: describe(e, o) });
            }
            (Ok(q), Some(Answer::Sat(model))) => {
                // A model of a query without the `forall` facts may break
                // them: shown only once checked against them.
                let (shown, broken) = if q.foralls { check_foralls(e, user, o, &defs, &model) } else { (Some(model.clone()), None) };
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
    // Without the values returned whose call is already reported.
    for (at, ks) in outside_posts.iter().filter(|g| g.1.len() > 1) {
        let os: Vec<&Obligation> = ks
            .iter()
            .map(|&k| obs[k])
            .filter(|o| !matches!(o.kind, ObKind::Post { at, .. } if bad_calls.contains(&at)))
            .collect();
        if let (false, Err(why)) = (os.is_empty(), &queries[ks[0]]) {
            v.diags[*at] = outside(e, &os, &why.0);
            post_fails.retain(|p| p.0 != *at);
        }
    }
        for (_, cases, at) in &uncovered {
        let d = v.diags[*at].clone();
        v.diags[*at] = merge_uncovered(d, cases);
    }
    for (k, at) in post_fails.into_iter().rev() {
        if bad_calls.contains(&at) && k < v.diags.len() {
            v.diags.remove(k);
        }
    }
    v.z3_version = z3_version();
    v.asked = ASKED.load(std::sync::atomic::Ordering::Relaxed) - asked0;
    v.reused = REUSED.load(std::sync::atomic::Ordering::Relaxed) - reused0;
    v
}

/// `obs` with, as facts, the values of the calls in each that are known at
/// compile time (§7.1, §8.9): the calls' values, never their functions'
/// bodies, each in `ledger` as computed. First, which functions recursing
/// by `decreasing` end whatever their preconditions say: their definitions
/// need no precondition guard (M17).
fn with_known_values(e: &Elab, obs: &[&Obligation], ledger: &mut Vec<LedgerEntry>) -> Vec<Obligation> {
    ends_everywhere(e, obs);
    obs.iter()
        .map(|o| {
            let known = known_calls(e, o);
            for (_, what) in &known {
                if !ledger.iter().any(|x| x.how == "computed" && x.span == o.span && x.what == *what) {
                    ledger.push(LedgerEntry { span: o.span, how: "computed", what: what.clone() });
                }
            }
            let mut o = (*o).clone();
            o.facts.extend(known.into_iter().map(|(f, _)| f));
            o
        })
        .collect()
}

/// Prove `obs` and the measures of `guesses`, of module `user`, now,
/// before the proofs phase, so that its functions can run while it is
/// checked (§8.9): the ledger's entries for them, and how many were
/// proved, if every one is; else None (the proofs phase then asks again, and reports what fails).
pub fn prove_now(e: &Elab, user: &str, obs: &[&Obligation], guesses: &[&crate::elab::termination::GuessGroup]) -> Option<(Vec<LedgerEntry>, usize)> {
    let mut v = Verified { diags: Vec::new(), ledger: Vec::new(), z3_version: None, proved: 0, asked: 0, reused: 0 };
    for g in guesses {
        if !guess_group(e, user, g, &mut v) {
            return None;
        }
    }
    let obs: Vec<&Obligation> = obs.iter().copied().filter(|o| o.only_if_nat.as_ref().is_none_or(|t| smt::is_nat(e, t))).collect();
    let (trivial, obs): (Vec<&Obligation>, Vec<&Obligation>) = obs.into_iter().partition(|o| {
        matches!(crate::core::force(&e.g, o.goal.clone()), crate::core::Val::Con(c, _) if Some(c) == e.g.well_known.true_con)
    });
    for o in trivial {
        v.proved += 1;
        v.ledger.push(LedgerEntry { span: o.span, how: "computed", what: describe(e, o) });
    }
    if obs.is_empty() {
        return Some((v.ledger, v.proved));
    }
    let with_values = with_known_values(e, &obs, &mut v.ledger);
    let obs: Vec<&Obligation> = with_values.iter().collect();
    let (_, queries, answers, _) = solve(e, user, &obs);
    for (o, (q, a)) in obs.iter().zip(queries.iter().zip(answers)) {
        let (Ok(_), Some(Answer::Unsat)) = (q, a) else { return None };
        v.proved += 1;
        v.ledger.push(LedgerEntry { span: o.span, how: "smt", what: describe(e, o) });
    }
    Some((v.ledger, v.proved))
}

/// Ask Z3 about `obs`, of module `user`: each one's query (or why it has
/// none), its answer, and whether a query proved it.
#[allow(clippy::type_complexity)]
fn solve(
    e: &Elab,
    user: &str,
    obs: &[&Obligation],
) -> (smt::Defs, Vec<Result<smt::Query, smt::Outside>>, Vec<Option<Answer>>, Vec<bool>) {
    // Translate on this thread (the elaborator isn't `Send`), solve in
    // parallel: each query's first ask (step 1) as soon as it is made.
    let defs = smt::Defs::default();
    let mut queries: Vec<Result<smt::Query, smt::Outside>> = Vec::with_capacity(obs.len());
    // The postconditions of calls in reflected bodies (#343) are given last:
    // most goals need none of them, and their axioms make Z3 search more in
    // every query. Steps 1 to 6 ask the query without them (the full query
    // where there are none): `unsat` is a proof, as from any weaker query;
    // where there are some, a model may break them, so `sat` is no
    // counterexample, and the full query decides (6b).
    let lean_of = |q: &smt::Query| q.without_bodies.clone().unwrap_or_else(|| q.text.clone());
    // 1. Everything, with a small work limit (D154): most goals need little
    //    work, and this query's answer is final either way: `unsat` is a
    //    proof, `sat` a real counterexample.
    let firsts = ask_produced(obs.len(), |k| {
        let q = smt::Builder::new(e, user).sharing(&defs).with_body_posts().query(obs[k]);
        let first = q.as_ref().ok().map(|q| with_limit(&lean_of(q), FIRST_RLIMIT));
        queries.push(q);
        first
    });
    let texts: Vec<Option<String>> = queries.iter().map(|q| q.as_ref().ok().map(|q| q.text.clone())).collect();
    let fallbacks: Vec<Option<String>> = queries.iter().map(|q| q.as_ref().ok().and_then(|q| q.without_axioms.clone())).collect();
    if std::env::var_os("CHECKERS_SMT_DUMP").is_some() {
        for (o, t) in obs.iter().zip(&texts) {
            eprintln!(";; ── {:?} at {:?}\n{}", o.kind, o.span, t.as_deref().unwrap_or(";; outside the fragment"));
        }
    }
    let lean: Vec<Option<String>> = queries.iter().map(|q| q.as_ref().ok().map(lean_of)).collect();
    let bodies: Vec<bool> = queries.iter().map(|q| q.as_ref().is_ok_and(|q| q.without_bodies.is_some())).collect();
    // Left for the full query.
    let mut with_bodies = vec![false; obs.len()];
    let mut answers: Vec<Option<Answer>> = firsts
        .into_iter()
        .enumerate()
        .map(|(k, a)| match a {
            Some(Answer::Unsat) => Some(Answer::Unsat),
            // The weaker queries would have models too.
            Some(Answer::Sat(_)) if bodies[k] => {
                with_bodies[k] = true;
                None
            }
            Some(a @ Answer::Sat(_)) => Some(a),
            _ => None,
        })
        .collect();
    // The obligations a query has proved.
    let mut proven: Vec<bool> = answers.iter().map(|a| matches!(a, Some(Answer::Unsat))).collect();
    // Z3 gave up: weaker queries, weakest first. `unsat` from a weaker query
    // is still a proof (§7.2).
    // 2. Definitions uninterpreted: fast when the facts in scope suffice.
    // 3. Only the definitions the goal mentions: Z3 doesn't unfold the
    //    functions whose results the facts in scope give.
    // 4. Only the definitions the facts in scope mention: the premises
    //    unfolded, not the goal's functions, which Z3 can unfold without end.
    // 5. Every definition, without the quantified postconditions of other
    //    functions, which can send Z3 searching (D101).
    // Each with the small work limit, then again with a larger one where Z3
    // gave up: a query that can't prove its goal often searches until its
    // limit.
    const TIERS: usize = 4;
    let weaker: Vec<[Option<&String>; TIERS]> = queries
        .iter()
        .zip(&answers)
        .zip(&with_bodies)
        .map(|((q, a), w)| match (q, a) {
            (Ok(q), None) if !w => [q.facts_only.as_ref(), q.focused.as_ref(), q.premised.as_ref(), q.without_axioms.as_ref()],
            _ => [None; TIERS],
        })
        .collect();
    // Whether each weaker query gave up with the small limit.
    let mut gave_up: Vec<[bool; TIERS]> = vec![[true; TIERS]; obs.len()];
    for limit in [FIRST_RLIMIT, QUICK_RLIMIT] {
        for tier in 0..TIERS {
            let ask_q: Vec<Option<String>> = weaker
                .iter()
                .enumerate()
                .map(|(k, w)| {
                    let t = w[tier]?;
                    // Asked already: proved, the same text as a weaker tier,
                    // or answered `sat` with the small limit.
                    if proven[k] || w[..tier].contains(&Some(t)) || !gave_up[k][tier] {
                        return None;
                    }
                    Some(with_limit(t, limit))
                })
                .collect();
            for (k, a) in ask_all(&ask_q).into_iter().enumerate() {
                match a {
                    Some(Answer::Unsat) => proven[k] = true,
                    Some(Answer::Sat(_)) => gave_up[k][tier] = false,
                    _ => {}
                }
            }
        }
    }
    // 6. Everything, with the full work limit: the query whose
    //    counterexample is real.
    let rest: Vec<Option<String>> = lean
        .iter()
        .enumerate()
        .map(|(k, t)| if proven[k] || answers[k].is_some() || with_bodies[k] { None } else { t.clone() })
        .collect();
    for (k, a) in ask_all(&rest).into_iter().enumerate() {
        if proven[k] {
            answers[k] = Some(Answer::Unsat);
        } else if matches!(a, Some(Answer::Unsat)) {
            proven[k] = true;
            answers[k] = a;
        } else if bodies[k] && rest[k].is_some() {
            with_bodies[k] = true;
        } else if a.is_some() {
            answers[k] = a;
        }
    }
    // 6b. With the postconditions of calls in reflected bodies, where the
    //     query has some and they could matter: with the small work limit,
    //     then the full one.
    for limit in [FIRST_RLIMIT, RLIMIT] {
        let full: Vec<Option<String>> = texts
            .iter()
            .enumerate()
            .map(|(k, t)| if with_bodies[k] { t.as_ref().map(|t| with_limit(t, limit)) } else { None })
            .collect();
        for (k, a) in ask_all(&full).into_iter().enumerate() {
            if full[k].is_none() {
                continue;
            }
            match a {
                Some(Answer::Unsat) => {
                    proven[k] = true;
                    answers[k] = a;
                    with_bodies[k] = false;
                }
                Some(Answer::Sat(_)) => {
                    answers[k] = a;
                    with_bodies[k] = false;
                }
                a if limit == RLIMIT => answers[k] = a,
                _ => {}
            }
        }
    }
    // 7. Z3 gave up on everything: a counterexample without the axioms, with
    //    the full work limit, is better than nothing (§7.2).
    let retry: Vec<Option<String>> = answers
        .iter()
        .zip(&fallbacks)
        .map(|(a, f)| if matches!(a, Some(Answer::Unknown(_))) { f.clone() } else { None })
        .collect();
    if retry.iter().any(|r| r.is_some()) {
        for (a, r) in answers.iter_mut().zip(ask_all(&retry)) {
            if let Some(r @ Answer::Sat(_)) = r {
                *a = Some(r);
            }
        }
    }
    (defs, queries, answers, proven)
}

/// Guess each recursive group's measure (D150): the first candidate, alone
/// and then in pairs compared lexicographically, that the prover shows every
/// recursive call makes smaller while staying a natural number. E0301 if
/// none is.
fn guess_measures(e: &Elab, user: &str, v: &mut Verified) {
    let early = e.early.borrow();
    for gr in e.guess_groups.iter().filter(|g| g.module == user && !early.guesses.contains(&g.members)) {
        guess_group(e, user, gr, v);
    }
}

/// Guess group `gr`'s measure (D150), as `guess_measures`: whether one is
/// proved.
fn guess_group(e: &Elab, user: &str, gr: &crate::elab::termination::GuessGroup, v: &mut Verified) -> bool {
    use crate::core::{eval, quote, Lit, Prim, Tm, Val};
    use crate::elab::termination::Measure;
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
    let (Some(tc), Some(fc)) = (wk.true_con, wk.false_con) else { return false };
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
    // Ask about the single measures, then the pairs, each first with a
    // small work limit (a measure that holds is usually quick to show,
    // and one that doesn't is slow to give up on), then the rest with
    // the quick one; take the first proved.
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
    let mut answers: Vec<Option<Answer>> = texts.iter().map(|_| None).collect();
    let singles = combos.iter().take_while(|c| c.iter().all(|m| m.0.len() == 1)).count();
    let small = |t: &Option<String>| {
        t.as_ref().map(|t| relimit(t, QUICK_RLIMIT, PROBE_RLIMIT))
    };
    let proved = |answers: &[Option<Answer>], ci: usize| {
        !obs[ci].is_empty() && answers[base[ci]..base[ci] + obs[ci].len()].iter().all(|a| matches!(a, Some(Answer::Unsat)))
    };
    let mut chosen: Option<usize> = None;
    'tiers: for limit in [true, false] {
        for tier in [0..singles, singles..combos.len()] {
            let ks: Vec<usize> = tier
                .clone()
                .filter(|ci| doomed[*ci].is_none())
                .flat_map(|ci| base[ci]..base[ci] + obs[ci].len())
                .filter(|k| !matches!(answers[*k], Some(Answer::Unsat)))
                .collect();
            let asked: Vec<Option<String>> = ks.iter().map(|k| if limit { small(&texts[*k]) } else { texts[*k].clone() }).collect();
            for (k, a) in ks.iter().zip(ask_all(&asked)) {
                answers[*k] = a;
            }
            if let Some(ci) = tier.clone().find(|ci| proved(&answers, *ci)) {
                chosen = Some(ci);
                break 'tiers;
            }
        }
    }
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
        Some(ci) => {
            for o in &obs[ci] {
                v.proved += 1;
                let mut what = describe(e, o);
                what.push_str(" (guessed)");
                v.ledger.push(LedgerEntry { span: o.span, how: "smt", what });
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
                return false;
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
                return false;
            }
            let who = if names.len() == 1 { format!("{} terminates", names[0]) } else { format!("{} terminate", names.join(", ")) };
            let mut d = Diagnostic::error("E0301", format!("cannot show that {who}: no measure found that every recursive call makes smaller"), at)
                .with_label("recursive call");
            d = d.with_note(note);
            v.diags.push(d.with_help("add `decreasing <measure>` as the first line of the function, or mark it `partial`"));
        }
    }
    chosen.is_some()
}

/// E0457: declarations whose conditions can never all hold, found by
/// proving `false` from them alone. Labelled by the conditions Z3's unsat
/// core names; a query Z3 gives up on reports nothing.
fn vacuous(e: &Elab, user: &str) -> Vec<Diagnostic> {
    let checks: Vec<&Vacuity> = e.vacuities.iter().filter(|c| c.ob.module == user).collect();
    if checks.is_empty() {
        return Vec::new();
    }
    let defs = smt::Defs::default();
    let texts: Vec<Option<String>> = checks
        .iter()
        .map(|c| {
            let q = smt::Builder::new(e, user).sharing(&defs).named_facts().query(&c.ob).ok()?;
            Some(with_limit(&q.facts_only.unwrap_or(q.text), VACUITY_RLIMIT))
        })
        .collect();
    if std::env::var_os("CHECKERS_SMT_DUMP").is_some() {
        for (c, t) in checks.iter().zip(&texts) {
            eprintln!(";; ── can `{}`'s conditions hold, at {:?}\n{}", c.name, c.at, t.as_deref().unwrap_or(";; outside the fragment"));
        }
    }
    let outs = ask_all_out(&texts);
    let mut out: Vec<Diagnostic> = Vec::new();
    // A type whose conditions can't hold: its constructors aren't reported too.
    let mut reported: Vec<Span> = Vec::new();
    for (c, o) in checks.iter().zip(outs) {
        let Some(o) = o else { continue };
        if !matches!(answer(o.clone()), Answer::Unsat) {
            continue;
        }
        let core = o.split_once('\n').map_or("", |r| r.1);
        if reported.contains(&c.at) || c.within.is_some_and(|t| reported.contains(&t)) {
            continue;
        }
        reported.push(c.at);
        // The core's facts, in the order written, and whether it needs
        // what the types say too.
        let names: Vec<&str> = core
            .lines()
            .next()
            .unwrap_or("")
            .split(|ch: char| ch.is_whitespace() || ch == '(' || ch == ')')
            .map(|w| w.trim_matches('|'))
            .collect();
        let core: Vec<usize> = names.iter().filter_map(|w| w.strip_prefix("fact.")?.parse().ok()).collect();
        let typed = names.iter().any(|w| w.starts_with("given."));
        let mut texts: Vec<&str> = Vec::new();
        for (k, t) in c.conds.iter().enumerate() {
            if let Some(t) = t {
                if core.contains(&k) && !texts.contains(&t.as_str()) {
                    texts.push(t);
                }
            }
        }
        // Only what the types say is needed (a class's type's predicates
        // are its values' type): each condition contributes to it.
        if texts.is_empty() && typed {
            texts = c.conds.iter().flatten().map(|t| t.as_str()).collect();
            texts.dedup();
        }
        out.push(vacuity_diag(c, &texts, typed));
    }
    out
}

/// The error for conditions of `c` that can't all hold; `texts`: those
/// the prover needed, as written; `typed`: and what the types say.
fn vacuity_diag(c: &Vacuity, texts: &[&str], typed: bool) -> Diagnostic {
    let n = &c.name;
    let (message, never) = match &c.kind {
        VacuityKind::Pre { params, lemma } => {
            let who = match params.as_slice() {
                [] => format!("`{n}`'s preconditions can never hold"),
                [p] => format!("no `{p}` meets `{n}`'s preconditions"),
                _ => format!("no arguments meet `{n}`'s preconditions"),
            };
            let never = if *lemma { format!("`{n}` could never be used") } else { format!("a call of `{n}` could never be made") };
            (who, never)
        }
        VacuityKind::TypeParams => (format!("no arguments meet the conditions on `{n}`'s parameters"), format!("`{n}` could never be applied")),
        VacuityKind::Fields => (format!("no fields meet `{n}`'s invariants"), format!("`{n}` could never be built")),
        VacuityKind::Alias { subject } => (format!("no `{subject}` meets `{n}`'s predicates"), format!("`{n}` has no values")),
        VacuityKind::ClassType { subject } => (format!("no `{subject}` meets the predicates on `{n}`"), format!("no instance could give `{n}` a type")),
    };
    let quoted: Vec<String> = texts.iter().map(|t| format!("`{t}`")).collect();
    let types = if typed { " for values of these types" } else { "" };
    let (label, fix) = match quoted.as_slice() {
        [] => ("these conditions can't all hold".to_string(), "remove or correct one of them"),
        [one] if typed => (format!("{one} can't hold{types}"), "remove or correct it"),
        [one] => (format!("{one} can never hold"), "remove or correct it"),
        [a, b] => (format!("{a} and {b} can't both hold{types}"), "remove or correct one of them"),
        [init @ .., last] => (format!("{} and {last} can't all hold{types}", init.join(", ")), "remove or correct one of them"),
    };
    Diagnostic::error("E0457", message, c.at).with_label(label).with_help(format!("{never}; {fix}"))
}

/// W022 (D144 d): the branches of the program's own used code whose facts
/// contradict each other, by the facts alone.
fn unreachable(e: &Elab, user: &str) -> Vec<Diagnostic> {
    if e.package_of(user) != "." {
        return Vec::new();
    }
    let inside = |a: Span, b: Span| b.start <= a.start && a.end <= b.end;
    let dead: Vec<Span> = e.dead.iter().filter(|(m, _)| m == user).map(|x| x.1).collect();
    let probes: Vec<&Probe> =
        e.probes.iter().filter(|p| p.ob.module == user && !dead.iter().any(|d| inside(p.ob.span, *d))).collect();
    if probes.is_empty() {
        return Vec::new();
    }
    let defs = smt::Defs::default();
    let texts: Vec<Option<String>> =
        probes
        .iter()
        .map(|p| {
            // Marked, so a cached answer is never taken for an obligation's.
            let q = smt::Builder::new(e, user).sharing(&defs).query(&p.ob).ok().map(|q| q.facts_only.unwrap_or(q.text));
            q.map(|t| with_limit(&t, PROBE_RLIMIT) + ";; reachable?\n")
        })
        .collect();
    let answers = ask_all(&texts);
    // A branch reached along several paths (an arm under several cases)
    // never runs only if no path reaches it.
    let mut groups: Vec<(Span, ProbeKind, bool, &Probe)> = Vec::new();
    for (p, a) in probes.iter().zip(&answers) {
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
    let o = &Obligation { text: crate::elab::first_line(&o.text), ..o.clone() };
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
        ObKind::Refines { class, member, pre: true, .. } => format!("`{member}` requires no more than class `{class}`: {}", o.text),
        ObKind::Refines { class, member, pre: false, .. } => format!("`{member}` promises what class `{class}` does: {}", o.text),
        ObKind::AtAlias { class, alias, member, .. } => format!("`{class}` at `{alias}`: `{member}` gives `{alias}`s: {}", o.text),
        ObKind::KnownResult { call, alias, .. } => format!("`{call}` is a `{alias}`: {}", o.text),
        ObKind::Auto => format!("auto: {}", o.text),
        ObKind::Have => format!("have {}", o.text),
        ObKind::Uncovered { case, binding: false } => format!("`match` needs no arm for {case}: it can't occur"),
        ObKind::Uncovered { case, binding: true } => format!("the pattern needn't cover {case}: it can't occur"),
    }
}

/// The calls in `o`'s goal and facts whose values are known at compile
/// time (`Elab::known_value`) and are numbers: each as the fact `call == n`
/// at `o`'s level, with how the ledger shows it. Only the calls `o` has, and
/// only outside binders, where the call is the same term in every case.
fn known_calls(e: &Elab, o: &Obligation) -> Vec<(crate::core::Val, String)> {
    use crate::core::{Lit, Prim, Tm, Val};
    fn number(e: &Elab, t: &Tm) -> bool {
        let (h, args) = t.spine();
        let Tm::Def(d) = h else { return false };
        let Some(info) = e.g.defs.get(d.0 as usize) else { return false };
        let empty = std::rc::Rc::new(Vec::new());
        let mut ty = crate::core::eval(&e.g, &empty, &info.ty);
        for k in 0..args.len() {
            let Val::Pi(_, _, _, _, c) = crate::core::force(&e.g, ty) else { return false };
            ty = crate::core::apply_closure(&e.g, &c, Val::var(usize::MAX / 2 + k));
        }
        e.type_range(&ty).is_some()
    }
    fn collect(e: &Elab, t: &Tm, depth: usize, out: &mut Vec<(Tm, i128)>) {
        if depth == 0 && number(e, t) {
            if let Some(Lit::Num(n)) = e.known_value(t) {
                if !out.iter().any(|(s, _)| crate::core::tm_eq(s, t)) {
                    out.push((t.clone(), n));
                }
                return;
            }
        }
        t.each_sub(|x, d| collect(e, x, depth + d, out));
    }
    let lvl = o.ctx.len();
    let mut found = Vec::new();
    for v in std::iter::once(&o.goal).chain(&o.facts) {
        collect(e, &quote(&e.g, lvl, v), 0, &mut found);
    }
    let env = std::rc::Rc::new((0..lvl).map(Val::var).collect::<Vec<_>>());
    let names: Vec<crate::core::Name> = o.ctx.iter().map(|l| l.name.clone()).collect();
    found
        .into_iter()
        .map(|(t, n)| {
            let fact = Tm::PrimApp(Prim::Eq, vec![t.clone(), Tm::Lit(Lit::Num(n))]);
            (crate::core::eval(&e.g, &env, &fact), format!("{} is {n}", crate::core::show(&e.g, &names, &t)))
        })
        .collect()
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
        let s = crate::core::show_marked(&e.g, &names, &quote(&e.g, lvl, f));
        // `… == True` and `… == False` by their text, the marks aside.
        let plain = crate::core::plain(&s);
        let lhs = s.rfind(" == ").map(|i| &s[..i]);
        let s = match (plain.ends_with(" == True").then_some(lhs).flatten(), plain.ends_with(" == False").then_some(lhs).flatten()) {
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
    // A block's first line: the rest is in a note (`in_full`).
    let o = &Obligation { text: crate::elab::first_line(&o.text), ..o.clone() };
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
            "add a `proof` block: `match` on a parameter or a call's result for case analysis, and `have` for facts it needs".into(),
        ),
        ObKind::ClassType { name, given } => (
            format!("cannot prove that every `{given}` satisfies `{}`, as `{name}` requires", o.text),
            format!("`{}` is `{given}` here", name.rsplit('.').next().unwrap_or(name)),
            format!("give `{}` a type whose values all satisfy it", name.rsplit('.').next().unwrap_or(name)),
        ),
        ObKind::Refines { class, member, pre: true, at: Some((x, mine, theirs)), .. } => (
            format!("`{member}` requires more of `{x}` than class `{class}` does"),
            format!("`{mine}` here, `{theirs}` in the class"),
            format!("a call through class `{class}` may pass any `{theirs}`: give `{x}` that type, or a type it implies"),
        ),
        ObKind::Refines { class, member, pre: false, at: Some((x, mine, theirs)), .. } => (
            format!("`{member}`'s result `{x}` doesn't promise what class `{class}`'s does"),
            format!("`{mine}` here, `{theirs}` in the class"),
            format!("give `{x}` the class's type `{theirs}`, or a type implying it"),
        ),
        ObKind::Refines { class, member, pre: true, .. } => (
            format!("`{member}` requires `{}`, which class `{class}` doesn't", o.text),
            "not implied by the class's preconditions".into(),
            format!("a call through class `{class}` needn't establish it: remove it, or check it in the body"),
        ),
        ObKind::Refines { class, member, pre: false, .. } => (
            format!("`{member}` doesn't promise `{}`, which class `{class}` does", o.text),
            format!("`{}` doesn't follow from this signature", o.text),
            format!("promise at least what class `{class}` does: add `{}` to this signature, or a condition implying it", o.text),
        ),
        ObKind::AtAlias { class, inst, alias, base, member, param: Some(p), .. } => (
            format!("`{class}` at `{alias}` runs `{base}`'s instance, whose `{member}` may give `{}` {}", p.name, p.gives),
            format!("`{class}` is used at `{alias}` here"),
            format!(
                "use `{base}` here, with a function that accepts every `{}`; or give `instance {inst}`'s `{member}` a signature in which `{}` is given only {}{}",
                p.accepts,
                p.name,
                p.only,
                p.example.as_ref().map_or(String::new(), |e| format!(", such as `{}~{e}`", p.name))
            ),
        ),
        ObKind::AtAlias { class, inst, alias, base, member, call, param: None, inside, whole: Some((wt, wb)) } => {
            // A part checked as one: the instance's signature can promise
            // it by its type, or for a list with `list.all`.
            let formula = (!o.text.is_empty()).then(|| o.text.clone());
            let promise = match &formula {
                Some(f) => format!("`{wt}` in its result, or `{f}` of it"),
                None => format!("`{wt}` in its result"),
            };
            match call {
                Some(c) => (
                    match (inside, &formula) {
                        (false, Some(f)) => format!("cannot prove that `{c}` has type `{wt}` (`{f} {}`)", if c.contains(' ') { format!("({c})") } else { c.clone() }),
                        (false, None) => format!("cannot prove that `{c}` has type `{wt}`"),
                        (true, _) => format!("cannot prove that the `{wb}` inside `{c}` has type `{wt}`"),
                    },
                    format!("`{class}` at `{alias}` runs `{base}`'s instance, and its `{member}` isn't shown to give a `{alias}` here"),
                    format!("use `{base}` here and check the result where a `{alias}` is needed; or promise it in a signature of `instance {inst}`'s `{member}`: {promise}"),
                ),
                None => (
                    if *inside {
                        format!("`{class}` at `{alias}` runs `{base}`'s instance, whose `{member}` isn't shown to give a value of type `{wt}` inside its result")
                    } else {
                        format!("`{class}` at `{alias}` runs `{base}`'s instance, whose `{member}` isn't shown to return a value of type `{wt}`")
                    },
                    format!("`{class}` is used at `{alias}` here, by code that may call `{member}` with any arguments"),
                    format!("use `{base}` here instead of `{alias}`; or promise it, for every argument, in a signature of `instance {inst}`'s `{member}`: {promise}"),
                ),
            }
        }
        ObKind::AtAlias { class, inst, alias, base, member, call: Some(c), param: None, inside, whole: None } => (
            match (inside, o.text.is_empty()) {
                (_, true) => format!("cannot prove that the `{alias}`s inside `{c}` are `{alias}`s"),
                (true, false) => format!("cannot prove `{}` of the `{alias}`s inside `{c}`", o.text),
                (false, false) => format!("cannot prove that `{c}` is a `{alias}` (`{}`)", o.text),
            },
            format!("`{class}` at `{alias}` runs `{base}`'s instance, and its `{member}` isn't shown to give a `{alias}` here"),
            format!("use `{base}` here and check the result where a `{alias}` is needed; or promise it in a signature of `instance {inst}`'s `{member}`"),
        ),
        ObKind::AtAlias { class, inst, alias, base, member, call: None, param: None, whole: None, .. } => (
            if o.text.is_empty() {
                format!("`{class}` at `{alias}` runs `{base}`'s instance, whose `{member}` isn't shown to return `{alias}`s")
            } else {
                format!("`{class}` at `{alias}` runs `{base}`'s instance, whose `{member}` isn't shown to return a `{alias}` (`{}`)", o.text)
            },
            format!("`{class}` is used at `{alias}` here, by code that may call `{member}` with any arguments"),
            format!("use `{base}` here instead of `{alias}`; or promise it, for every argument, in a signature of `instance {inst}`'s `{member}`"),
        ),
        ObKind::KnownResult { call, alias, inside, pres, inst, member } => (
            if *inside {
                format!("cannot prove `{}` of the `{alias}`s inside `{call}`", o.text)
            } else {
                format!("cannot prove that `{call}` is a `{alias}` (`{}`)", o.text)
            },
            if *inside { format!("the class promises `{alias}`s in the result only where {pres}") } else { format!("the class promises a `{alias}` only where {pres}") },
            if *inside {
                format!("make the call meet the class's precondition, or have `instance {inst}`'s `{member}` promise `{alias}`s in its result at these arguments too")
            } else {
                format!("make the call meet the class's precondition, or have `instance {inst}`'s `{member}` promise a `{alias}` at these arguments too")
            },
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
    let code = match o.kind {
        ObKind::Uncovered { .. } => "E0240",
        ObKind::Refines { .. } => "E0371",
        ObKind::AtAlias { .. } => "E0456",
        _ => "E0450",
    };
    let mut d = Diagnostic::error(code, msg, o.span).with_label(label).with_notes(in_full(o));
    if let ObKind::Refines { class, declared, at, .. } = &o.kind {
        d = d.with_note(format!("class `{class}` declares `{declared}`"));
        if at.is_some() {
            d = d.with_note(format!("it needs `{}`", crate::elab::first_line(&o.text)));
        }
    }
    if let ObKind::Weaken { .. } = &o.kind {
        d = d.with_note(format!("it needs `{}`", crate::elab::first_line(&o.text)));
    }
    if let ObKind::KnownResult { inst, member, .. } = &o.kind {
        d = d.with_note(format!("this calls `instance {inst}`'s `{member}`, whose signature requires less than the class's and doesn't promise it here"));
    }
    if let Some(n) = returned(e, o) {
        d = d.with_note(n);
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
        format!("`{}` {what}: here the prover knows only its postconditions, the values of its calls known at compile time, and the lemmas you bring in with `have`", info.name)
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

/// One obligation outside what the prover handles, or the same one for
/// several values returned, each with its facts.
fn outside(e: &Elab, os: &[&Obligation], why: &str) -> Diagnostic {
    let o = os[0];
    let (msg, label, _) = headline(o);
    let code = if matches!(o.kind, ObKind::Uncovered { .. }) { "E0240" } else { "E0451" };
    let mut d = Diagnostic::error(code, msg, o.span)
        .with_label(label)
        .with_notes(in_full(o))
        .with_note(format!("this obligation is outside what the prover handles: it involves {why}"));
    if let [o] = os {
        d = d.with_notes(returned(e, o)).with_notes(facts_note(e, o));
    } else {
        for o in os {
            let r = returned(e, o).unwrap_or_default();
            d = d.with_note(match facts_note(e, o) {
                Some(f) => format!("{r}; {f}"),
                None => r,
            });
        }
    }
    d.with_help("state the fact you need as a lemma and bring it in with `have`")
}

/// A predicate written on several lines (a `match`), shown in full: the
/// message has only its first line.
fn in_full(o: &Obligation) -> Option<String> {
    o.text.contains('\n').then(|| {
        let body: Vec<String> = o.text.lines().map(|l| format!("    {l}")).collect();
        format!("`{}` in full:\n{}", crate::elab::first_line(&o.text), body.join("\n"))
    })
}

/// Which returned value a postcondition is about: its line and text.
fn returned(e: &Elab, o: &Obligation) -> Option<String> {
    let ObKind::Post { at, .. } = &o.kind else { return None };
    let f = e.sources.get(&o.module)?;
    let (line, _) = f.line_col(at.start);
    let text: String = f.text.get(at.start as usize..at.end as usize).unwrap_or("").split_whitespace().collect::<Vec<_>>().join(" ");
    Some(format!("for the value returned on line {line}: `{text}`"))
}

/// Check Z3's counterexample against the `forall` facts in scope, which its
/// query left out (D137): the same query with them given to Z3, quantified,
/// first with the model's values fixed, then free. A model of that query is
/// a counterexample; without one, the note saying why none is shown.
fn check_foralls(e: &Elab, user: &str, o: &Obligation, defs: &smt::Defs, model: &str) -> (Option<String>, Option<String>) {
    let why = |broken: bool| {
        Some(format!(
            "no counterexample: the one Z3 found {} a `forall` in scope, which the prover uses only by name, with `have`",
            if broken { "breaks" } else { "could not be checked against" }
        ))
    };
    let Ok(q) = smt::Builder::new(e, user).sharing(defs).with_body_posts().with_foralls().query(o) else { return (None, why(false)) };
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
    let broken = match ask(&pinned) {
        Answer::Sat(m) => return (Some(m), None),
        Answer::Unsat => true,
        Answer::Unknown(_) => false,
    };
    match ask(&text) {
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
        out += &format!("{}:{line}:{col}  {:<8} {}\n", file.name, x.how, x.what);
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

#[cfg(test)]
mod tests {
    /// Queries solved at the same time with different work limits (two
    /// programs checked on two threads) each run with their own: the small
    /// limit always gives up, the large one always proves.
    #[test]
    fn each_query_runs_with_its_own_work_limit() {
        const GOAL: &str = "(set-logic ALL)\n(declare-const x (_ BitVec 5))\n(declare-const y (_ BitVec 5))\n(declare-const z (_ BitVec 5))\n(assert (not (= (bvmul x (bvadd y z)) (bvadd (bvmul x y) (bvmul x z)))))\n(check-sat)\n";
        let said = |limit: u64| {
            std::thread::spawn(move || {
                let query = super::options(limit) + GOAL;
                let mut said: Vec<String> = (0..500).map(|_| super::run_z3(&query)).collect();
                said.dedup();
                said
            })
        };
        let threads = [said(50), said(50_000_000), said(50), said(50_000_000)];
        let said: Vec<Vec<String>> = threads.into_iter().map(|t| t.join().unwrap()).collect();
        let (gave_up, proved) = (vec!["unknown\n".to_string()], vec!["unsat\n".to_string()]);
        assert_eq!(said, [gave_up.clone(), proved.clone(), gave_up, proved]);
    }
}
