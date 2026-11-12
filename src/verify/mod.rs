//! The prover pipeline (SPEC §7, M3): obligations → SMT-LIB → Z3 → diagnostics
//! and the trust ledger.

pub mod smt;

use crate::core::{quote, show};
use crate::diag::Diagnostic;
use crate::elab::{Elab, ObKind, Obligation, WeakenRole};
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

/// A weaker query, tried first: with the smaller work limit.
fn quick(q: Option<String>) -> Option<String> {
    q.map(|t| t.replacen(&format!("(set-option :rlimit {RLIMIT})"), &format!("(set-option :rlimit {QUICK_RLIMIT})"), 1))
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
    ASKED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let out = match cached(query) {
        Some(out) => {
            REUSED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            out
        }
        None => {
            let start = std::time::Instant::now();
            let out = run_z3(query);
            let cut_off = out.starts_with("unknown") && start.elapsed().as_millis() as u64 >= SAFETY_MS * 9 / 10;
            if !cut_off {
                store(query, &out);
            }
            out
        }
    };
    answer(out)
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
    let workers = std::thread::available_parallelism().map_or(2, |n| n.get()).min(8);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let results: Vec<std::sync::Mutex<Option<Answer>>> = texts.iter().map(|_| std::sync::Mutex::new(None)).collect();
    std::thread::scope(|s| {
        for _ in 0..workers {
            // Z3 recurses deeply on large terms: give it a big stack.
            let worker = std::thread::Builder::new().stack_size(512 << 20);
            let spawned = worker.spawn_scoped(s, || loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(t) = texts.get(i) else { break };
                if let Some(t) = t {
                    let a = ask(t);
                    *results[i].lock().unwrap_or_else(|e| e.into_inner()) = Some(a);
                }
            });
            if spawned.is_err() {
                break;
            }
        }
    });
    results.into_iter().map(|m| m.into_inner().unwrap_or_else(|e| e.into_inner())).collect()
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
pub fn verify(e: &Elab, user: &str) -> Verified {
    let obs: Vec<&Obligation> = e
        .obligations
        .iter()
        .filter(|o| o.module == user)
        .filter(|o| o.only_if_nat.as_ref().is_none_or(|t| smt::is_nat(e, t)))
        .collect();
    let mut v = Verified { diags: Vec::new(), ledger: Vec::new(), z3_version: None, proved: 0, asked: 0, reused: 0 };
    let (asked0, reused0) = (ASKED.load(std::sync::atomic::Ordering::Relaxed), REUSED.load(std::sync::atomic::Ordering::Relaxed));
    for t in e.admits.iter().filter(|t| t.module == user) {
        v.ledger.push(LedgerEntry { span: t.span, how: "trusted", what: t.what.clone(), hash: None });
    }
    for t in e.builtin_axioms.iter().filter(|t| t.module == user) {
        v.ledger.push(LedgerEntry { span: t.span, how: "axiom", what: t.what.clone(), hash: None });
    }
    for (m, span, _) in e.checks.iter().filter(|c| c.0 == user) {
        let _ = m;
        let text = e.sources.get(user).and_then(|f| f.text.get(span.start as usize..span.end as usize)).unwrap_or("");
        v.ledger.push(LedgerEntry { span: *span, how: "computed", what: format!("check {}", text.trim()), hash: None });
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
        v.ledger.push(LedgerEntry { span: o.span, how: "computed", what: describe(e, o), hash: None });
    }
    if obs.is_empty() {
        return v;
    }
    // Which functions recursing by `decreasing` end whatever their
    // preconditions say: their definitions need no precondition guard (M17).
    ends_everywhere(e, &obs);
    // Translate on this thread (the elaborator isn't `Send`), solve in parallel.
    let defs = smt::Defs::default();
    let queries: Vec<Result<smt::Query, smt::Outside>> = obs.iter().map(|o| smt::Builder::new(e, user).sharing(&defs).query(o)).collect();
    let texts: Vec<Option<String>> = queries.iter().map(|q| q.as_ref().ok().map(|q| q.text.clone())).collect();
    let fallbacks: Vec<Option<String>> = queries.iter().map(|q| q.as_ref().ok().and_then(|q| q.without_axioms.clone())).collect();
    if std::env::var_os("CHECKERS_SMT_DUMP").is_some() {
        for (o, t) in obs.iter().zip(&texts) {
            eprintln!(";; ── {:?} at {:?}\n{}", o.kind, o.span, t.as_deref().unwrap_or(";; outside the fragment"));
        }
    }
    // Weakest first: `unsat` from a weaker query is still a proof (§7.2).
    // 1. Definitions uninterpreted: fast when the facts in scope suffice.
    let quick_q: Vec<Option<String>> = queries.iter().map(|q| quick(q.as_ref().ok().and_then(|q| q.facts_only.clone()))).collect();
    let quick_answers = ask_all(&quick_q);
    let proved_quick: Vec<bool> = quick_answers.iter().map(|a| matches!(a, Some(Answer::Unsat))).collect();
    // 2. Only the definitions the goal mentions: Z3 doesn't unfold the
    //    functions whose results the facts in scope give.
    let focus: Vec<Option<String>> = queries
        .iter()
        .zip(&proved_quick)
        .map(|(q, p)| if *p { None } else { quick(q.as_ref().ok().and_then(|q| q.focused.clone())) })
        .collect();
    let proved_focus: Vec<bool> = ask_all(&focus).iter().map(|a| matches!(a, Some(Answer::Unsat))).collect();
    let proved_quick: Vec<bool> = proved_quick.iter().zip(&proved_focus).map(|(a, b)| *a || *b).collect();
    // 3. Every definition, without the quantified postconditions of other
    //    functions, which can send Z3 searching (D101).
    let lean: Vec<Option<String>> =
        fallbacks.iter().zip(&proved_quick).map(|(f, p)| if *p { None } else { quick(f.clone()) }).collect();
    let proved_lean: Vec<bool> = ask_all(&lean).iter().map(|a| matches!(a, Some(Answer::Unsat))).collect();
    // 4. Everything: the query whose counterexample is real.
    let rest: Vec<Option<String>> = texts
        .iter()
        .zip(proved_quick.iter().zip(&proved_lean))
        .map(|(t, (q, l))| if *q || *l { None } else { t.clone() })
        .collect();
    let mut answers = ask_all(&rest);
    for (k, a) in answers.iter_mut().enumerate() {
        if proved_quick[k] || proved_lean[k] {
            *a = Some(Answer::Unsat);
        }
    }
    // 5. Z3 gave up on everything: a counterexample without the axioms, with
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
    for (k, ((o, q), a)) in obs.iter().zip(&queries).zip(answers).enumerate() {
        match (q, a) {
            (Err(why), _) => v.diags.push(outside(e, o, &why.0)),
            (Ok(q), Some(Answer::Unsat)) => {
                v.proved += 1;
                // The query that was proved, as Z3 was given it.
                let text = match (&q.facts_only, &q.without_axioms) {
                    _ if proved_focus[k] => quick(q.focused.clone()),
                    (Some(t), _) if proved_quick[k] => quick(Some(t.clone())),
                    (_, Some(t)) if proved_lean[k] => quick(Some(t.clone())),
                    _ => Some(q.text.clone()),
                };
                let hash = text.map(|t| fnv(&t));
                v.ledger.push(LedgerEntry { span: o.span, how: "smt", what: describe(e, o), hash });
            }
            (Ok(q), Some(Answer::Sat(model))) => {
                let mut d = failed(e, o, Some(render_model(&model, &q.shown, &q.string_vars, &q.array_vars)));
                if !q.dropped.is_empty() {
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
    v.z3_version = z3_version();
    v.asked = ASKED.load(std::sync::atomic::Ordering::Relaxed) - asked0;
    v.reused = REUSED.load(std::sync::atomic::Ordering::Relaxed) - reused0;
    v
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
        ObKind::CownInvariant { alias } => format!("cown contents stay `{alias}`: {}", o.text),
        ObKind::Refined { alias, value } => format!("`{value}` is a `{alias}`: {}", o.text),
        ObKind::Weaken { sub, sup, .. } => format!("every `{sub}` is a `{sup}`: {}", o.text),
        ObKind::NatSub => format!("`Nat` subtraction `{}` stays at or above zero", o.text),
        ObKind::Measure { func, measure } => format!("termination of `{func}`: `decreasing {measure}` gets smaller"),
        ObKind::Div => format!("divisor of `{}` is not zero", o.text),
        ObKind::Index => format!("index in bounds: {}", o.text),
        ObKind::Lemma { name } => format!("lemma `{name}`: {}", o.text),
        ObKind::Auto => format!("auto: {}", o.text),
        ObKind::Have => format!("have {}", o.text),
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
            "check it first (`if a >= b then a - b else …`), or use `Int`".into(),
        ),
        ObKind::Div => (
            "cannot prove that the divisor is not zero".into(),
            "`/` and `%` need a non-zero right side".into(),
            "check the divisor first, e.g. `if d != 0 then n / d else …`".into(),
        ),
        ObKind::Index => (
            format!("cannot prove that the index is in bounds (`{}`)", o.text),
            "indexing needs `i < len src`".into(),
            "check the index first, e.g. `if i < len src then src[i] else …`".into(),
        ),
        ObKind::Lemma { name } => (
            format!("cannot prove lemma `{name}`"),
            format!("`{}`", o.text),
            "add a `proof` block: `match` on a parameter for case analysis, and `have` for facts it needs".into(),
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
    }
}

fn failed(e: &Elab, o: &Obligation, model: Option<String>) -> Diagnostic {
    let (msg, label, help) = headline(o);
    let mut d = Diagnostic::error("E0450", msg, o.span).with_label(label);
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
    if let Some(n) = facts_note(e, o) {
        d = d.with_note(n);
    }
    // Sealed functions from other modules (D54) are only known by their contracts.
    let mut sealed = Vec::new();
    let lvl = o.ctx.len();
    crate::elab::collect_sealed(&quote(&e.g, lvl, &o.goal), &e.g, &o.module, &mut sealed);
    let sealed_note = sealed.first().map(|d| {
        let info = &e.g.defs[d.0 as usize];
        format!(
            "`{}` is sealed in `{}`: here the prover knows only its postconditions and the lemmas you bring in with `have`",
            info.name, info.module
        )
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
    let mut d = Diagnostic::error("E0451", msg, o.span)
        .with_label(label)
        .with_note(format!("this obligation is outside what the prover handles: it involves {why}"));
    if let Some(n) = facts_note(e, o) {
        d = d.with_note(n);
    }
    d.with_help("state the fact you need as a lemma and bring it in with `have`")
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
