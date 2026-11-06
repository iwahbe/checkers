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
}

enum Answer {
    Unsat,
    Sat(String),
    Unknown(String),
}

/// Z3 reports API misuse through an error handler; the default one may exit
/// the process. SMT-LIB errors come back in the output text instead.
unsafe extern "C" fn ignore_error(_: z3_sys::Z3_context, _: z3_sys::Z3_error_code) {}

/// The linked-in Z3's version (D46).
pub fn z3_version() -> Option<String> {
    // SAFETY: Z3_get_full_version returns a static, NUL-terminated string.
    let v = unsafe { std::ffi::CStr::from_ptr(z3_sys::Z3_get_full_version()) };
    Some(format!("Z3 {}", v.to_string_lossy()))
}

/// Evaluate one SMT-LIB script in a fresh Z3 context.
fn ask(query: &str) -> Answer {
    let Ok(text) = std::ffi::CString::new(query) else { return Answer::Unknown("a NUL byte in the query".into()) };
    // SAFETY: the config and context are created, used and deleted on this
    // thread only; the returned string is copied before the context is deleted.
    let out = unsafe {
        let Some(cfg) = z3_sys::Z3_mk_config() else { return Answer::Unknown("Z3 could not start".into()) };
        let Some(ctx) = z3_sys::Z3_mk_context(cfg) else {
            z3_sys::Z3_del_config(cfg);
            return Answer::Unknown("Z3 could not start".into());
        };
        z3_sys::Z3_set_error_handler(ctx, Some(ignore_error));
        let r = z3_sys::Z3_eval_smtlib2_string(ctx, text.as_ptr());
        let out = if r.is_null() { String::new() } else { std::ffi::CStr::from_ptr(r).to_string_lossy().into_owned() };
        z3_sys::Z3_del_context(ctx);
        z3_sys::Z3_del_config(cfg);
        out
    };
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

/// Prove the obligations of module `user` (§7.2).
pub fn verify(e: &Elab, user: &str) -> Verified {
    let obs: Vec<&Obligation> = e
        .obligations
        .iter()
        .filter(|o| o.module == user)
        .filter(|o| o.only_if_nat.as_ref().is_none_or(|t| smt::is_nat(e, t)))
        .collect();
    let mut v = Verified { diags: Vec::new(), ledger: Vec::new(), z3_version: None, proved: 0 };
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
    // Translate on this thread (the elaborator isn't `Send`), solve in parallel.
    let queries: Vec<Result<smt::Query, smt::Outside>> = obs.iter().map(|o| smt::Builder::new(e, user).query(o)).collect();
    let texts: Vec<Option<String>> = queries.iter().map(|q| q.as_ref().ok().map(|q| q.text.clone())).collect();
    let fallbacks: Vec<Option<String>> = queries.iter().map(|q| q.as_ref().ok().and_then(|q| q.without_axioms.clone())).collect();
    if std::env::var_os("CHECKERS_SMT_DUMP").is_some() {
        for (o, t) in obs.iter().zip(&texts) {
            eprintln!(";; ── {:?} at {:?}\n{}", o.kind, o.span, t.as_deref().unwrap_or(";; outside the fragment"));
        }
    }
    // First with definitions uninterpreted: `unsat` there is a proof (§7.2).
    let quick: Vec<Option<String>> = queries.iter().map(|q| q.as_ref().ok().and_then(|q| q.facts_only.clone())).collect();
    let quick_answers = ask_all(&quick);
    let proved_quick: Vec<bool> = quick_answers.iter().map(|a| matches!(a, Some(Answer::Unsat))).collect();
    let rest: Vec<Option<String>> = texts.iter().zip(&proved_quick).map(|(t, p)| if *p { None } else { t.clone() }).collect();
    let mut answers = ask_all(&rest);
    for (a, p) in answers.iter_mut().zip(&proved_quick) {
        if *p {
            *a = Some(Answer::Unsat);
        }
    }
    // `unknown` with the quantified axioms: try without them (§7.2).
    let retry: Vec<Option<String>> = answers
        .iter()
        .zip(&fallbacks)
        .map(|(a, f)| if matches!(a, Some(Answer::Unknown(_))) { f.clone() } else { None })
        .collect();
    if retry.iter().any(|r| r.is_some()) {
        for (a, r) in answers.iter_mut().zip(ask_all(&retry)) {
            if let Some(r) = r {
                if !matches!(r, Answer::Unknown(_)) {
                    *a = Some(r);
                }
            }
        }
    }
    for (k, ((o, q), a)) in obs.iter().zip(&queries).zip(answers).enumerate() {
        match (q, a) {
            (Err(why), _) => v.diags.push(outside(e, o, &why.0)),
            (Ok(q), Some(Answer::Unsat)) => {
                v.proved += 1;
                let text = match (&q.facts_only, proved_quick[k]) {
                    (Some(t), true) => t,
                    _ => &q.text,
                };
                v.ledger.push(LedgerEntry { span: o.span, how: "smt", what: describe(e, o), hash: Some(fnv(text)) });
            }
            (Ok(q), Some(Answer::Sat(model))) => {
                let mut d = failed(e, o, Some(render_model(&model, &q.shown, &q.string_vars)));
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
    let mut shown: Vec<String> = Vec::new();
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

fn render_model(text: &str, shown: &[(String, String)], strings: &[String]) -> String {
    let sx = parse_sx(text);
    let Some(Sx::List(pairs)) = sx.first() else { return String::new() };
    let mut found: Vec<(usize, String)> = Vec::new();
    for p in pairs {
        if let Sx::List(kv) = p {
            if let (Some(Sx::Atom(k)), Some(v)) = (kv.first(), kv.get(1)) {
                if let Some(pos) = shown.iter().position(|(n, _)| n == k) {
                    let v = unlet(v, &[]);
                    let s = match seq_bytes(&v) {
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
