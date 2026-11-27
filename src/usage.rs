//! Usage checking (QTT, §2 and §4): `own` values are used exactly once on
//! every path; `ghost` values never at runtime.

use crate::core::{CaseTm, DefId, Mult, Prim, Tm, Val};
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::elab::Elab;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Count {
    Zero,
    One,
    Many,
}

impl Count {
    fn add(self, o: Count) -> Count {
        match (self, o) {
            (Count::Zero, x) | (x, Count::Zero) => x,
            _ => Count::Many,
        }
    }
    fn scale(self, m: Mult) -> Count {
        match (self, m) {
            (_, Mult::Zero) | (Count::Zero, _) => Count::Zero,
            (c, Mult::One) => c,
            (_, Mult::Many) => Count::Many,
        }
    }
}

struct Binder {
    name: String,
    mult: Mult,
    /// Where it is bound, if the elaborator recorded it (#672 d).
    span: Option<Span>,
    /// A lambda's parameter: `own` comes from the function type it is
    /// checked against, not from anything written.
    lambda: bool,
    /// A lambda parameter's resource type, when known (`File`).
    resource: Option<String>,
    /// Bound to a closure that uses a resource (or an `own` value), or to a
    /// value that holds one or an `own` value: it must be used exactly once
    /// (#658, §8.4).
    oneshot: Option<Once>,
    /// Its type, where known: what a `match` on it takes out.
    ty: Option<BTy>,
}

/// Why a binder must be used exactly once though its type doesn't say so.
#[derive(Clone)]
struct Once {
    /// What `kind` names: a resource, an `own` value, a function.
    used: String,
    kind: Kind,
    /// The named binder it was taken from, for a binder the program
    /// doesn't name (`$field0`, `$s`).
    origin: Option<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// It is, or holds, a closure that uses the resource (or `own` value) `used`.
    Uses,
    /// It holds the `own` value `used`.
    Own,
    /// It is, or holds, the result of `used`, declared `own`.
    Result,
}

/// What `carried` finds in a term.
#[derive(Default)]
struct Carried {
    lvls: BTreeSet<usize>,
    /// A call of a function whose result is declared `own`: the function,
    /// and the call's span (empty for a call the compiler made).
    call: Option<(String, crate::core::Pos)>,
}

#[derive(Clone)]
enum BTy {
    Tm(std::rc::Rc<Tm>),
    Val(Val),
}

struct U<'a> {
    e: &'a mut Elab,
    did: DefId,
    binders: Vec<Binder>,
    reported: bool,
    /// Binder level → a function it was passed to whose parameter isn't `own` (#545).
    /// The function each `own` binder is passed to as a parameter that isn't
    /// `own`, with its module and the call's span.
    copied_by: std::collections::HashMap<usize, (String, String, Option<Span>)>,
    /// The `own` binders a closure captures.
    captured: std::collections::BTreeSet<usize>,
    /// The term being checked is the function's result.
    tail: bool,
    /// The function's result type, where known.
    ret: Option<Val>,
    /// The function's result is declared `own`.
    ret_own: bool,
    /// The function's result type, as written in its type.
    ret_tm: Option<Tm>,
    /// Whether a definition's result may hold a value that must be used
    /// once, by definition: asked at each call `carried` looks through.
    result_holds: std::cell::RefCell<std::collections::HashMap<DefId, bool>>,
}

/// Each binder's uses, by level: only the binders used at all, so that a
/// term's counts take room for the variables it mentions, not for every
/// binder in scope.
type Counts = BTreeMap<usize, Count>;

fn add(a: &mut Counts, b: &Counts) {
    for (l, y) in b {
        let x = a.entry(*l).or_insert(Count::Zero);
        *x = x.add(*y);
    }
}

/// The uses of the binder at `lvl`.
fn count(c: &Counts, lvl: usize) -> Count {
    c.get(&lvl).copied().unwrap_or(Count::Zero)
}

/// Each use made `m` times.
fn scaled(c: Counts, m: Mult) -> Counts {
    c.into_iter().map(|(l, x)| (l, x.scale(m))).filter(|(_, x)| *x != Count::Zero).collect()
}

impl U<'_> {
    fn zero(&self) -> Counts {
        Counts::new()
    }

    fn report(&mut self, lvl: usize, c: Count, mixed: bool) {
        let b = &self.binders[lvl];
        // A field read or index that would drop part of it was reported (E0406, E0407).
        if self.e.part_reported.contains(&(self.did, b.name.to_string())) {
            return;
        }
        let meta = self.e.fn_meta.get(&self.did).cloned().unwrap_or_default();
        let resource = match (&b.resource, b.span) {
            (Some(t), Some(s)) => Some((s, t.clone())),
            _ => self.e.resource_vars.get(&(self.did, b.name.clone())).cloned(),
        };
        let span = match (&resource, b.span) {
            (_, Some(s)) => s,
            (Some((s, _)), None) => *s,
            (None, None) => meta
                .params
                .iter()
                .find(|p| p.0 == b.name)
                .map(|p| p.2)
                .or_else(|| self.e.local_spans.get(&(self.did, b.name.to_string())).copied())
                .unwrap_or(meta.span),
        };
        let fname = meta.name.clone();
        let name = b.name.clone();
        if let Some(once) = b.oneshot.clone() {
            self.report_once(lvl, &once, c, mixed, span);
            return;
        }
        if let (Some((_, ty)), Mult::One) = (&resource, b.mult) {
            let d = match (mixed, c) {
                (true, _) => Diagnostic::error(
                    "E0402",
                    format!("`{name}` holds a resource (`{ty}`), but `{fname}` uses it on some paths and not on others"),
                    span,
                )
                .with_help("a resource must be used exactly once on every path, e.g. closed in every branch"),
                (false, Count::Zero) => Diagnostic::error(
                    "E0401",
                    format!("`{name}` holds a resource (`{ty}`), so it must be used exactly once, but `{fname}` never uses it"),
                    span,
                )
                .with_help(if crate::core::plain(ty).starts_with("Future ") {
                    "join it: a future of a resource is one too, joined exactly once"
                } else {
                    "close it, or pass it on"
                }),
                _ => {
                    let d = Diagnostic::error(
                        "E0401",
                        format!("`{name}` holds a resource (`{ty}`), so it must be used exactly once, but `{fname}` may use it more than once"),
                        span,
                    );
                    let closure = self.captured.contains(&lvl) && self.cown_target(lvl).is_none();
                    match self.copied_by.get(&lvl).filter(|_| !closure) {
                        // A cown can't hold a resource (#643 k).
                        Some((_, module, _)) if self.cown_target(lvl).is_some() => {
                            let what = self.cown_target(lvl).unwrap_or_default();
                            let short = module.trim_start_matches("std.");
                            // At the call that puts it there.
                            let span = self.copied_at(lvl).unwrap_or(span);
                            Diagnostic::error(
                                "E0405",
                                format!("`{name}` holds a resource (`{ty}`), which can't be put in {what}"),
                                span,
                            )
                            .with_note(format!(
                                "`{name}` is passed to `{short}.new`; a cown's handle can be shared, so nothing would make sure what it holds is closed"
                            ))
                            .with_help("keep the resource with one owner, passing it on through calls, `fork` and `join`; a cown may hold the rest of the state")
                        }
                        Some((callee, ..)) => d
                            .with_note(format!("`{name}` is passed to `{callee}`, whose parameter is not `own`, so `{callee}` may copy or drop it"))
                            .with_help(format!("mark that parameter of `{callee}` with `own` (as in `x~own a`) so it can take a resource")),
                        None if self.captured.contains(&lvl) && self.copied_by.contains_key(&lvl) => {
                            let callee = self.copied_by.get(&lvl).map(|c| c.0.clone()).unwrap_or_default();
                            Diagnostic::error(
                                "E0401",
                                format!("`{name}` holds a resource (`{ty}`), and a closure that uses it may be called more than once, or never"),
                                span,
                            )
                            .with_note(format!("a closure using `{name}` is passed to `{callee}`, whose parameter is not `own`, so `{callee}` may call it any number of times"))
                            .with_help(format!("mark that parameter of `{callee}` with `own` (as in `f~own (Unit -> a)`)"))
                        }
                        None if self.captured.contains(&lvl) => Diagnostic::error(
                            "E0401",
                            format!("`{name}` holds a resource (`{ty}`), and a closure that uses it may be called more than once, or never"),
                            span,
                        )
                        .with_note("a closure that uses a resource must be called exactly once: called where it is made, bound with `let` and called once, or passed to a parameter declared `own`")
                        .with_help(format!("pass the closure to an `own` parameter (`f~own (Unit -> a)`), or make `{name}` a parameter of the closure")),
                        None if crate::core::plain(ty).starts_with("Future ") => {
                            d.with_help("join it once: a future of a resource is one too, joined exactly once")
                        }
                        None => d.with_help("a resource can't be copied: each operation on it gives back the one to use next, `let (x, f) = op f`"),
                    }
                }
            };
            self.e.err(d);
            self.reported = true;
            return;
        }
        let guard = self.e.guard_vars.get(&(self.did, name.clone())).copied();
        let d = match (b.mult, mixed, c) {
            (Mult::Zero, _, _) if guard.is_some() => Diagnostic::error(
                "E0408",
                format!("this guard uses `{name}`, a resource, which the arm's body needs"),
                guard.unwrap_or(span),
            )
            .with_label("the guard runs before the body, so it can't use the resource")
            .with_help(format!("test `{name}` inside the arm's body instead, with `if` or another `match`")),
            (Mult::Zero, _, _) => {
                // Where it is used at run time, if the elaborator saw it.
                let used = self.e.ghost_uses.get(&(self.did, name.clone())).and_then(|v| v.first().copied());
                let d = Diagnostic::error(
                    "E0403",
                    format!("`{name}` is `ghost`: it may only appear in types and constraints, but `{fname}` uses it at runtime"),
                    used.unwrap_or(span),
                );
                match used {
                    Some(_) => d.with_label("used at runtime here"),
                    None => d,
                }
                .with_help("remove `ghost` if the value is needed at runtime")
            }
            (_, true, _) => Diagnostic::error(
                "E0402",
                format!("`{name}` is `own`, but `{fname}` uses it on some paths and not on others"),
                span,
            )
            .with_help("an `own` value must be used exactly once on every path"),
            (_, false, c) if b.lambda && b.span.is_some() && resource.is_none() && self.cown_target(lvl).is_none() => Diagnostic::error(
                "E0401",
                format!(
                    "this closure's parameter `{name}` must be used exactly once, but the closure {}",
                    if c == Count::Zero { "never uses it" } else { "may use it more than once" }
                ),
                span,
            )
            .with_notes(self.copied_by.get(&lvl).map(|(callee, ..)| {
                format!("`{name}` is passed to `{callee}`, whose parameter is not `own`, so `{callee}` may copy or drop it")
            }))
            .with_help(format!("the closure's type takes `{name}` as `own`, since its type may be a resource: use it exactly once")),
            (_, false, Count::Zero) => Diagnostic::error(
                "E0401",
                format!("`{name}` is `own`, so it must be used exactly once, but `{fname}` never uses it"),
                span,
            )
            .with_help("`own` promises a single use, so the argument may be a resource that must not be dropped; use it, or remove `own`"),
            _ if self.cown_target(lvl).is_some() => Diagnostic::error(
                "E0405",
                format!("`{name}` is `own`, so it may be a resource, which can't be put in {}", self.cown_target(lvl).unwrap_or_default()),
                self.copied_at(lvl).unwrap_or(span),
            )
            .with_help("remove `own`: a cown holds only values that aren't resources"),
            _ => Diagnostic::error(
                "E0401",
                format!("`{name}` is `own`, so it must be used exactly once, but `{fname}` may use it more than once"),
                span,
            )
            .with_help("`own` promises a single use, so the argument may be a resource; remove `own` if the value must be used twice"),
        };
        self.e.err(d);
        self.reported = true;
    }

    /// Whether a binder's value is a function.
    fn is_fn(&self, lvl: usize) -> bool {
        let ty = match &self.binders[lvl].ty {
            Some(BTy::Tm(t)) => self.e.eval_open(t),
            Some(BTy::Val(v)) => v.clone(),
            None => return false,
        };
        matches!(self.e.force(&ty), Val::Pi(..))
    }

    /// The name, span and kind (a closure, or a value holding one) of a
    /// binder that must be used once, as the program names it: one it
    /// doesn't name (`$field0`) is told by the binder it came from.
    fn once_subject(&self, lvl: usize, once: &Once, span: Span) -> (String, Span, bool, bool) {
        let b = &self.binders[lvl];
        let own_fn = |l: usize| self.is_fn(l);
        match once.origin.filter(|_| b.name.starts_with('$')) {
            Some(o) => {
                let ob = &self.binders[o];
                let span = ob.span.or_else(|| self.e.local_spans.get(&(self.did, ob.name.clone())).copied()).unwrap_or(span);
                (ob.name.clone(), span, own_fn(o), true)
            }
            None => (b.name.clone(), span, own_fn(lvl), b.name.starts_with('$')),
        }
    }

    /// What a binder that must be used once is, for a message: `` `k` uses
    /// `file`, a resource, so it must be called exactly once ``.
    fn once_what(name: &str, once: &Once, func: bool) -> (String, &'static str) {
        let used = &once.used;
        let (verb, done) = if func { ("call", "called") } else { ("use", "used") };
        let what = match (once.kind, func) {
            (Kind::Uses, true) => format!("`{name}` uses `{used}`, a resource"),
            (Kind::Uses, false) => format!("`{name}` holds a closure that uses `{used}`, a resource"),
            (Kind::Own, true) => format!("`{name}` comes from `{used}`, which is `own`"),
            (Kind::Own, false) => format!("`{name}` holds `{used}`, which is `own`"),
            (Kind::Result, true) => format!("`{name}` is the result of `{used}`, declared `own`"),
            (Kind::Result, false) => format!("`{name}` holds the result of `{used}`, declared `own`"),
        };
        (format!("{what}, so it must be {done} exactly once"), verb)
    }

    /// What a binder that must be used once holds, for a message about a
    /// value without a name (`let _ = …`).
    fn once_thing(once: &Once) -> String {
        let used = &once.used;
        match once.kind {
            Kind::Uses => format!("a closure that uses `{used}`, a resource"),
            Kind::Own => format!("a value holding `{used}`, which is `own`"),
            Kind::Result => format!("the result of `{used}`, declared `own`"),
        }
    }

    fn report_once(&mut self, lvl: usize, once: &Once, c: Count, mixed: bool, span: Span) {
        let fname = self.e.fn_meta.get(&self.did).map(|m| m.name.clone()).unwrap_or_default();
        let (name, span, func, unnamed) = self.once_subject(lvl, once, span);
        let (what, verb) = Self::once_what(&name, once, func);
        let d = match (mixed, c) {
            (false, Count::Zero) if name == "_" => {
                Diagnostic::error("E0401", format!("this drops {}", Self::once_thing(once)), span)
                    .with_label("it must be used exactly once")
                    .with_help("bind it to a name, then use it")
            }
            (true, _) => Diagnostic::error("E0402", format!("{what}, but `{fname}` {verb}s it on some paths and not on others"), span),
            (false, Count::Zero) if unnamed => Diagnostic::error("E0401", format!("{what}, but a pattern in `{fname}` discards it"), span)
                .with_help(format!("bind it to a name in the pattern, and {verb} it")),
            (false, Count::Zero) => Diagnostic::error("E0401", format!("{what}, but `{fname}` never {verb}s it"), span)
                .with_help(format!("{verb} `{name}`, or pass it on to a parameter declared `own`")),
            _ => {
                let d = Diagnostic::error("E0401", format!("{what}, but `{fname}` may {verb} it more than once"), span);
                match self.copied_by.get(&lvl) {
                    Some((callee, ..)) => d
                        .with_note(format!("`{name}` is passed to `{callee}`, whose parameter is not `own`, so `{callee}` may {verb} it any number of times"))
                        .with_help(format!("mark that parameter of `{callee}` with `own` (as in `f~own (Unit -> a)`)")),
                    None if func && once.kind == Kind::Uses => d.with_help("a closure that uses a resource is used up by its call"),
                    None if func && once.kind == Kind::Result => d.with_help(format!("the result of `{}` is used up by its call, as a resource is by its use", once.used)),
                    None if func => d.with_help("a function taken from an `own` value is used up by its call"),
                    None if once.kind == Kind::Own => d.with_help(format!("a value holding `{}` is used up by its use, as `{}` is", once.used, once.used)),
                    None => d.with_help("a value holding a closure that must be called once is used up by its use, as the closure is"),
                }
            }
        };
        self.e.err(d);
        self.reported = true;
    }

    /// The help for a function that returns what must be used once but
    /// doesn't declare its result `own`.
    fn declare_own(&self) -> String {
        let r = self.e.fn_meta.get(&self.did).and_then(|m| m.result.clone()).unwrap_or_else(|| "r".into());
        let ty = match &self.ret_tm {
            Some(t) if {
                let mut fv = BTreeSet::new();
                crate::core::free_vars(t, 0, &mut fv);
                fv.is_empty()
            } =>
            {
                let shown = self.e.show_val(&crate::elab::Cx::default(), &self.e.eval_open(t));
                if shown.contains(' ') { format!("({shown})") } else { shown }
            }
            _ => "…".into(),
        };
        format!("declare the result `own` (`{r}~own {ty}`), so that the caller uses it exactly once, as it would a resource")
    }

    /// `at`, a call's span, or the function's name for a call the compiler
    /// made.
    fn at_or_fn(&self, at: crate::core::Pos) -> Span {
        at.span().or_else(|| self.e.fn_meta.get(&self.did).map(|m| m.span)).unwrap_or_default()
    }

    /// Where a binder is bound, for a message.
    fn span_of(&self, lvl: usize) -> Span {
        let b = &self.binders[lvl];
        let meta = self.e.fn_meta.get(&self.did);
        b.span
            .or_else(|| self.e.local_spans.get(&(self.did, b.name.clone())).copied())
            .or_else(|| meta.and_then(|m| m.params.iter().find(|p| p.0 == b.name).map(|p| p.2)))
            .unwrap_or_else(|| meta.map(|m| m.span).unwrap_or_default())
    }

    /// `t` is the function's result, which isn't declared `own`: a closure
    /// that must be called once, or a value holding one, can't be it, since
    /// its type doesn't tell the caller to call it once (§8.4).
    fn escape(&mut self, t: &Tm) {
        if self.ret_own || !self.ret.as_ref().is_none_or(|r| self.e.may_hold_once(r)) {
            return;
        }
        let fname = self.e.fn_meta.get(&self.did).map(|m| m.name.clone()).unwrap_or_default();
        // A closure made here.
        if let Some(used) = self.oneshot_use(t) {
            let Some(lvl) = self.binders.iter().rposition(|b| b.name == used) else { return };
            let span = self.span_of(lvl);
            let d = Diagnostic::error("E0401", format!("`{fname}` returns a closure that uses `{used}`, a resource, so it must be called exactly once"), span)
                .with_note(format!("`{fname}`'s result isn't declared `own`, so its caller may call it any number of times, or never"))
                .with_help(self.declare_own());
            self.e.err(d);
            self.reported = true;
            // Reported once.
            self.binders[lvl].mult = Mult::Many;
            return;
        }
        let found = self.carried_all(t);
        if let Some((callee, at)) = found.call {
            let span = self.at_or_fn(at);
            self.e.err(
                Diagnostic::error("E0401", format!("`{fname}` returns the result of `{callee}`, declared `own`, so it must be used exactly once"), span)
                    .with_note(format!("`{fname}`'s result isn't declared `own`, so its caller may use it any number of times, or never"))
                    .with_help(self.declare_own()),
            );
            self.reported = true;
            return;
        }
        let Some(lvl) = found.lvls.into_iter().find(|l| self.binders[*l].oneshot.as_ref().is_some_and(|o| o.kind != Kind::Own)) else {
            return;
        };
        let Some(once) = self.binders[lvl].oneshot.clone() else { return };
        let span = self.span_of(lvl);
        let (name, span, func, _) = self.once_subject(lvl, &once, span);
        let (what, verb) = Self::once_what(&name, &once, func);
        self.e.err(
            Diagnostic::error("E0401", format!("{what}, but `{fname}` returns it"), span)
                .with_note(format!("`{fname}`'s result isn't declared `own`, so its caller may {verb} it any number of times, or never"))
                .with_help(self.declare_own()),
        );
        self.reported = true;
        // Reported once.
        self.binders[lvl].oneshot = None;
        self.binders[lvl].mult = Mult::Many;
    }

    /// Check a binder's own usage when it goes out of scope.
    fn close(&mut self, counts: &Counts) {
        let lvl = self.binders.len() - 1;
        let c = count(counts, lvl);
        match self.binders[lvl].mult {
            Mult::One if c != Count::One => self.report(lvl, c, false),
            Mult::Zero if c != Count::Zero => self.report(lvl, c, false),
            _ => {}
        }
    }

    fn under(&mut self, name: &crate::core::Name, mult: Mult, body: &Tm, lambda: bool, ty: Option<BTy>, oneshot: Option<Once>) -> Counts {
        let span = self.e.binder_span(name);
        let resource = if lambda { self.e.lam_resource(name) } else { None };
        self.binders.push(Binder { name: name.to_string(), mult, span, lambda, resource, oneshot, ty });
        let c = self.go(body);
        self.close(&c);
        self.binders.pop();
        let mut c = c;
        c.remove(&self.binders.len());
        c
    }

    /// The call that passes a binder to a parameter that isn't `own`, if
    /// it came from the source.
    fn copied_at(&self, lvl: usize) -> Option<Span> {
        self.copied_by.get(&lvl).and_then(|c| c.2)
    }

    /// What a binder passed to `cown.new` or `actor.new` would be put in: a
    /// cown can't hold a resource (#643 k).
    fn cown_target(&self, lvl: usize) -> Option<String> {
        match self.copied_by.get(&lvl).map(|(c, m, _)| (c.as_str(), m.as_str())) {
            Some(("new", "std.cown")) => Some("a cown".into()),
            Some(("new", "std.actor")) => Some("an actor's state".into()),
            _ => None,
        }
    }

    fn go(&mut self, t: &Tm) -> Counts {
        // Only a `let`'s body and a `match`'s arms are in its place.
        let tail = std::mem::take(&mut self.tail);
        if tail && !matches!(t, Tm::Let(..) | Tm::Case(..)) {
            self.escape(t);
            // A result declared `own` is used once, by the caller: a
            // closure made there is called once.
            if self.ret_own && matches!(t, Tm::Lam(..) | Tm::App(..)) && !head_is_meta(t) {
                return self.go_once(t);
            }
        }
        match t {
            Tm::Var(i) => {
                let lvl = self.binders.len() - 1 - i;
                Counts::from([(lvl, Count::One)])
            }
            // An unsolved meta (an error was reported) uses nothing.
            Tm::App(..) if head_is_meta(t) => self.zero(),
            Tm::App(..) => self.app(t, false, None),
            Tm::Lam(x, m, _, b) => {
                let m = &if *m == Mult::One && self.e.lam_own_moot(x) { Mult::Many } else { *m };
                // A closure may run any number of times.
                let c = self.under(x, *m, b, true, None, None);
                for (lvl, n) in &c {
                    if *n != Count::Zero && self.binders[*lvl].mult == Mult::One {
                        self.captured.insert(*lvl);
                    }
                }
                scaled(c, Mult::Many)
            }
            Tm::Let(x, m, ty, v, b) => {
                // A tuple pattern binds each component (`$c0`, `$c1`, …) by
                // projecting the tuple: together they use it once, counted
                // at the first.
                let rest_of_tuple = x.starts_with("$c") && matches!(&**v, Tm::Proj(t, i, _) if *i > 0 && matches!(**t, Tm::Var(_)));
                let scale = if *m == Mult::Zero || rest_of_tuple { Mult::Zero } else { Mult::One };
                // A closure that uses a resource, bound by `let`: the
                // variable is used once instead (#658).
                if let (Some(used), false) = (self.oneshot_use(v), *m == Mult::Zero) {
                    let mut c = self.go_once(v);
                    let once = Once { used, kind: Kind::Uses, origin: None };
                    self.tail = tail;
                    let cb = self.under(x, Mult::One, b, false, Some(BTy::Tm(ty.clone())), Some(once));
                    add(&mut c, &cb);
                    return c;
                }
                // A value built from one that must be used exactly once must
                // be too, if its type can hold that part (§8.4).
                let once = match *m {
                    Mult::Many => self.holder(v).filter(|_| {
                        let tv = self.e.eval_open(ty);
                        self.e.may_hold_once(&tv) && !self.e.val_linear(&tv)
                    }),
                    _ => None,
                };
                let mult = if once.is_some() { Mult::One } else { *m };
                let mut c = scaled(self.go(v), scale);
                self.tail = tail;
                let cb = self.under(x, mult, b, false, Some(BTy::Tm(ty.clone())), once);
                add(&mut c, &cb);
                c
            }
            Tm::Tuple(v) => {
                let mut c = self.zero();
                for x in v {
                    let cx = self.go(x);
                    add(&mut c, &cx);
                }
                c
            }
            Tm::ConApp(cid, v) => {
                let g = &self.e.g;
                let ci = &g.cons[cid.0 as usize];
                let np = g.arity_ty(ci.ty);
                let mults: Vec<Mult> =
                    std::iter::repeat_n(Mult::Zero, np).chain(ci.fields.iter().map(|f| f.1)).collect();
                let mut c = self.zero();
                for (x, m) in v.iter().zip(mults) {
                    let cx = scaled(self.go(x), if m == Mult::Zero { Mult::Zero } else { Mult::One });
                    add(&mut c, &cx);
                }
                c
            }
            Tm::PrimApp(p, v) => {
                let mut c = self.zero();
                // The type `Nat` subtraction and indexing carry is erased.
                let n = if matches!(p, Prim::Sub | Prim::Index) { 2 } else { v.len() };
                for x in v.iter().take(n) {
                    // Behaviour bodies run once: a resource may move into them.
                    let cx = match (p, x) {
                        (Prim::When, Tm::Lam(..)) => self.lam_once(x),
                        _ => self.go(x),
                    };
                    add(&mut c, &cx);
                }
                c
            }
            Tm::Proj(x, _, _) | Tm::Field(x, _, _, _) => self.go(x),
            Tm::Case(s, c) => {
                let mut cs = self.go(s);
                let scrut = match &**s {
                    Tm::Var(i) => Some(self.binders.len() - 1 - i),
                    _ => None,
                };
                // What the arms take out of a value that must be used once
                // must be used once too.
                let holder = self.holder(s);
                let sty = scrut.and_then(|l| self.binders[l].ty.clone()).map(|t| match t {
                    BTy::Tm(t) => self.e.eval_open(&t),
                    BTy::Val(v) => v,
                });
                let cb = self.case(c, scrut, holder, sty, tail);
                add(&mut cs, &cb);
                cs
            }
            // Types and globals are erased or contain no locals.
            _ => self.zero(),
        }
    }

    /// The binders (levels) whose value may be part of the value of `t`: the
    /// variables it is built from, everything a closure or partial application
    /// captures, and the arguments of a call whose result may be a resource.
    /// When unsure, every variable `t` mentions.
    fn carried(&self, t: &Tm) -> BTreeSet<usize> {
        self.carried_all(t).lvls
    }

    /// `carried`, and a call in it whose result is declared `own`.
    fn carried_all(&self, t: &Tm) -> Carried {
        let mut out = Carried::default();
        self.carried_into(t, 0, &mut out);
        out
    }

    /// `depth`: binders `t` is under that aren't in `self.binders`.
    fn carried_into(&self, t: &Tm, depth: usize, out: &mut Carried) {
        let all = |t: &Tm, depth: usize, out: &mut Carried| {
            let mut fv = std::collections::BTreeSet::new();
            crate::core::free_vars(t, depth, &mut fv);
            for i in fv {
                if let Some(l) = self.binders.len().checked_sub(1 + i) {
                    out.lvls.insert(l);
                }
            }
        };
        match t {
            Tm::Var(i) if *i >= depth => {
                if let Some(l) = self.binders.len().checked_sub(1 + (i - depth)) {
                    out.lvls.insert(l);
                }
            }
            Tm::Var(_) | Tm::Lit(_) | Tm::Known(_) | Tm::Def(_) | Tm::Con(_) | Tm::Univ(_) | Tm::TyCon(_) | Tm::Error => {}
            Tm::Tuple(v) | Tm::ConApp(_, v) => v.iter().for_each(|x| self.carried_into(x, depth, out)),
            Tm::Proj(x, _, _) | Tm::Field(x, _, _, _) => self.carried_into(x, depth, out),
            // A call with effects is the call (§7.1).
            Tm::PrimApp(Prim::Effect(_), v) => v.iter().for_each(|x| self.carried_into(x, depth, out)),
            Tm::Let(_, _, _, v, b) => {
                self.carried_into(v, depth, out);
                self.carried_into(b, depth + 1, out);
            }
            Tm::App(.., at) => {
                // Erased arguments (types, `ghost` values) carry nothing.
                let mut head = t;
                let mut args = Vec::new();
                let mut n = 0;
                while let Tm::App(f, a, _, m, _) = head {
                    if *m != Mult::Zero {
                        args.push(&**a);
                    }
                    n += 1;
                    head = f;
                }
                match head {
                    // A constructor stores its arguments.
                    Tm::Con(_) => args.into_iter().for_each(|x| self.carried_into(x, depth, out)),
                    // A saturated call carries its arguments only if its
                    // result may hold one of them (§8.4).
                    Tm::Def(d) => {
                        let ty = &self.e.g.defs[d.0 as usize].ty;
                        // A result that is a function adds to the Π-type's
                        // binders: a definition's own are its parameters.
                        let arity = self.e.fn_meta.get(d).map_or_else(|| pi_arity(ty).0, |m| m.n_binders());
                        let result = pi_peel(ty, arity);
                        let holds = || *self.result_holds.borrow_mut().entry(*d).or_insert_with(|| self.e.may_hold_once(&self.e.eval_open(result)));
                        if n >= arity && out.call.is_none() && self.e.fn_meta.get(d).is_some_and(|m| m.result_own) {
                            out.call = Some((self.e.g.defs[d.0 as usize].name.to_string(), *at));
                        }
                        if n < arity || holds() {
                            args.into_iter().for_each(|x| all(x, depth, out));
                        }
                    }
                    _ => {
                        all(head, depth, out);
                        args.into_iter().for_each(|x| all(x, depth, out));
                    }
                }
            }
            // Numbers, truth values, strings: nothing is carried.
            Tm::PrimApp(
                Prim::Add
                | Prim::Sub
                | Prim::Mul
                | Prim::Div
                | Prim::Rem
                | Prim::Neg
                | Prim::Eq
                | Prim::Ne
                | Prim::Lt
                | Prim::Le
                | Prim::Gt
                | Prim::Ge
                | Prim::Concat
                | Prim::Len,
                _,
            ) => {}
            // A closure, a match, an element, a builtin: everything they mention.
            _ => all(t, depth, out),
        }
    }

    /// An application. `once`: it is in a place that calls the closure it
    /// makes, if it is a partial application, exactly once. `whole`: the
    /// span of the call `t` is the function of, if it is one.
    fn app(&mut self, t: &Tm, once: bool, whole: Option<Span>) -> Counts {
        let Tm::App(f, a, _, m, at) = t else { return self.go(t) };
        // The whole call, for a message about passing `a` (`cown.new f s`,
        // not `cown.new f`).
        let call = whole.or(at.span());
        // A lambda called where it is made runs once (#658).
        let mut c = match &**f {
            Tm::Lam(..) => self.lam_once(f),
            // The rest of this call: what it partly applies is decided at the top.
            Tm::App(..) => self.app(f, true, call),
            _ => self.go(f),
        };
        // A constructor stores its argument: one use, like a saturated `ConApp`.
        let m = if *m != Mult::Zero && head_is_con(f) { Mult::One } else { *m };
        // A lambda passed to an `own` parameter is called once (#658).
        let used = if m == Mult::One { self.go_once(a) } else { self.go(a) };
        // Arguments are evaluated once, before the call: only what can be
        // part of the argument's value is used as often as the parameter
        // allows; a use inside it (`f` in `g (close f)`) happens once.
        let found = self.carried_all(a);
        let carried = found.lvls;
        // The result of a call declared `own`, passed where it may be
        // copied or dropped.
        if let (Mult::Many, Some((f, at)), Some(callee)) = (m, &found.call, head_def(f).map(|d| self.e.g.defs[d.0 as usize].name.to_string())) {
            if !self.reported {
                let fname = self.e.fn_meta.get(&self.did).map(|m| m.name.clone()).unwrap_or_default();
                let span = self.at_or_fn(*at);
                self.e.err(
                    Diagnostic::error("E0401", format!("the result of `{f}` is declared `own`, so it must be used exactly once, but `{fname}` passes it to `{callee}`"), span)
                        .with_note(format!("the parameter of `{callee}` is not `own`, so `{callee}` may use it any number of times, or never"))
                        .with_help(format!("mark that parameter of `{callee}` with `own` (as in `f~own (Unit -> a)`)")),
                );
                self.reported = true;
            }
        }
        if m == Mult::Many {
            if let Some(callee) = head_def(f).map(|d| {
                let d = &self.e.g.defs[d.0 as usize];
                (d.name.to_string(), d.module.to_string(), call)
            }) {
                for (lvl, c) in &used {
                    if *c != Count::Zero && self.binders[*lvl].mult == Mult::One && carried.contains(lvl) {
                        self.copied_by.entry(*lvl).or_insert_with(|| callee.clone());
                    }
                }
            }
        }
        // An erased argument (a type, a ghost value) uses nothing at all,
        // even what it only computes from (`a` in `wrap s a`).
        let ca: Counts = used
            .into_iter()
            .map(|(lvl, x)| (lvl, if m == Mult::Zero || carried.contains(&lvl) { x.scale(m) } else { x }))
            .filter(|(_, x)| *x != Count::Zero)
            .collect();
        add(&mut c, &ca);
        // A partial application holding a resource is a closure that
        // uses it: unless this is a place that calls it once, it may
        // be called any number of times (#658).
        if !once && self.partial_use(t).is_some() {
            for (lvl, x) in c.iter_mut() {
                if *x != Count::Zero && self.binders[*lvl].mult == Mult::One {
                    *x = Count::Many;
                    self.captured.insert(*lvl);
                }
            }
        }
        c
    }

    /// `t` where what it makes is called exactly once: a lambda, or a
    /// partial application, holding a resource (#658).
    fn go_once(&mut self, t: &Tm) -> Counts {
        match t {
            Tm::Lam(..) => self.lam_once(t),
            Tm::App(..) if !head_is_meta(t) => self.app(t, true, None),
            _ => self.go(t),
        }
    }

    /// If `t` partly applies a function to an argument that holds a
    /// resource (`close_with file` for a function of two parameters), the
    /// name of one such argument.
    fn partial_use(&self, t: &Tm) -> Option<String> {
        let d = head_def(t)?;
        let meta = self.e.fn_meta.get(&d)?;
        let args = t.spine().1;
        if args.len() >= meta.n_binders() {
            return None;
        }
        args.into_iter()
            .flat_map(|a| self.carried(a))
            .find(|l| self.binders[*l].mult == Mult::One)
            .map(|l| self.binders[l].name.clone())
    }

    /// If `t` is a closure that uses a resource or an `own` value, the
    /// name of one it uses: such a closure must be called exactly once (#658).
    fn oneshot_use(&self, t: &Tm) -> Option<String> {
        if matches!(t, Tm::App(..)) {
            return self.partial_use(t);
        }
        if !matches!(t, Tm::Lam(..)) {
            return None;
        }
        let mut fv = std::collections::BTreeSet::new();
        crate::core::free_vars(t, 0, &mut fv);
        fv.into_iter()
            .filter_map(|i| self.binders.len().checked_sub(1 + i))
            .find(|l| self.binders[*l].mult == Mult::One)
            .map(|l| self.binders[l].name.clone())
    }

    /// If the value of `t` may be built from a value that must be used
    /// exactly once (a resource, an `own` value, a closure that uses one, or
    /// a value holding one), why that one must be.
    fn holder(&self, t: &Tm) -> Option<Once> {
        // A closure that must be called once, if one: it says most.
        let found = self.carried_all(t);
        let carried = found.lvls;
        let lvl = carried
            .iter()
            .find(|l| self.binders[**l].oneshot.as_ref().is_some_and(|o| o.kind == Kind::Uses))
            .or_else(|| carried.iter().find(|l| self.binders[**l].mult == Mult::One));
        let Some(&lvl) = lvl else {
            return found.call.map(|(f, _)| Once { used: f, kind: Kind::Result, origin: None });
        };
        let b = &self.binders[lvl];
        let named = (!b.name.starts_with('$')).then_some(lvl);
        Some(match &b.oneshot {
            Some(o) => Once { used: o.used.clone(), kind: o.kind, origin: named.or(o.origin) },
            // A resource the value may hold, as a closure that uses it does.
            None if self.is_resource(lvl) => Once { used: b.name.clone(), kind: Kind::Uses, origin: None },
            None => Once { used: b.name.clone(), kind: Kind::Own, origin: named },
        })
    }

    /// Whether a binder holds a resource by its type.
    fn is_resource(&self, lvl: usize) -> bool {
        let b = &self.binders[lvl];
        b.resource.is_some()
            || self.e.resource_vars.contains_key(&(self.did, b.name.clone()))
            || match &b.ty {
                Some(BTy::Tm(t)) => self.e.type_linear(t),
                Some(BTy::Val(v)) => self.e.val_linear(v),
                None => false,
            }
    }

    fn lam_once(&mut self, t: &Tm) -> Counts {
        match t {
            Tm::Lam(x, m, _, b) => {
                let m = &if *m == Mult::One && self.e.lam_own_moot(x) { Mult::Many } else { *m };
                self.binders.push(Binder { name: x.to_string(), mult: *m, span: self.e.binder_span(x), lambda: true, resource: self.e.lam_resource(x), oneshot: None, ty: None });
                let c = self.lam_once(b);
                self.close(&c);
                self.binders.pop();
                let mut c = c;
                c.remove(&self.binders.len());
                c
            }
            other => self.go(other),
        }
    }

    fn case(&mut self, c: &CaseTm, scrut: Option<usize>, holder: Option<Once>, sty: Option<Val>, tail: bool) -> Counts {
        let args = sty.map(|t| self.e.force(&t)).and_then(|t| match t {
            Val::TyCon(_, args) => Some(args),
            _ => None,
        });
        let mut results: Vec<Counts> = Vec::new();
        // Per result, the variables that hold no resource in that arm.
        let mut moots: Vec<Vec<usize>> = Vec::new();
        for (con, n, body) in &c.branches {
            if matches!(body, Tm::Error) {
                continue;
            }
            let start = self.binders.len();
            // Variables whose type, refined in this arm, holds no resource
            // (#664): used any number of times here, as if exactly once.
            let moot: Vec<usize> = match scrut {
                Some(s) => self
                    .e
                    .moot_in_arm
                    .range((self.did, s, *con, 0)..(self.did, s, *con, start))
                    .map(|k| k.3)
                    .filter(|l| self.binders[*l].mult == Mult::One)
                    .collect(),
                None => Vec::new(),
            };
            for l in &moot {
                self.binders[*l].mult = Mult::Many;
            }
            let fields = self.e.con_field_types(*con, args.as_deref().filter(|a| a.len() == self.e.g.arity_ty(self.e.g.cons[con.0 as usize].ty)));
            for k in 0..*n {
                let ty = fields.get(k).map(|f| f.1.clone());
                // A field that can hold what made the scrutinee single-use.
                let once = holder.clone().filter(|_| {
                    fields.get(k).is_none_or(|(m, t)| *m != Mult::Zero && self.e.may_hold_once(t) && !self.e.val_linear(t))
                });
                let mult = if once.is_some() { Mult::One } else { Mult::Many };
                self.binders.push(Binder { name: format!("$field{k}"), mult, span: None, lambda: false, resource: None, oneshot: once, ty: ty.map(BTy::Val) });
            }
            self.tail = tail;
            let mut r = self.go(body);
            for lvl in (start..start + n).rev() {
                let k = count(&r, lvl);
                if self.binders[lvl].mult == Mult::One && k != Count::One && !self.reported {
                    self.report(lvl, k, false);
                }
            }
            self.binders.truncate(start);
            r.split_off(&start);
            for l in &moot {
                self.binders[*l].mult = Mult::One;
            }
            results.push(r);
            moots.push(moot);
        }
        for (_, body) in &c.lits {
            if !matches!(body, Tm::Error) {
                self.tail = tail;
                results.push(self.go(body));
                moots.push(Vec::new());
            }
        }
        if let Some(d) = c.default.as_ref().filter(|d| !matches!(d, Tm::Error)) {
            self.tail = tail;
            results.push(self.go(d));
            moots.push(Vec::new());
        }
        // Branches without code (errors already reported) don't constrain usage.
        let mut out = self.zero();
        if results.is_empty() {
            return out;
        }
        // Only a binder some arm uses, or holds no resource in, can count
        // as other than unused.
        let used: BTreeSet<usize> = results.iter().flat_map(|r| r.keys()).chain(moots.iter().flatten()).copied().collect();
        for lvl in used {
            let mult = self.binders[lvl].mult;
            // An arm where it holds no resource doesn't constrain it (#664);
            // if none does, it counts as used once.
            let all: Vec<Count> =
                results.iter().zip(&moots).filter(|(_, m)| !m.contains(&lvl)).map(|(r, _)| count(r, lvl)).collect();
            let Some(first) = all.first().copied() else {
                out.insert(lvl, Count::One);
                continue;
            };
            if mult == Mult::One && all.iter().any(|x| *x != first) && !self.reported {
                let has_one = all.contains(&Count::One);
                let has_zero = all.contains(&Count::Zero);
                if has_one && has_zero {
                    self.report(lvl, Count::One, true);
                }
            }
            let k = all.iter().copied().fold(Count::Zero, |a, b| match (a, b) {
                (Count::Many, _) | (_, Count::Many) => Count::Many,
                (Count::One, _) | (_, Count::One) => Count::One,
                _ => Count::Zero,
            });
            if k != Count::Zero {
                out.insert(lvl, k);
            }
        }
        out
    }
}

fn head_def(t: &Tm) -> Option<DefId> {
    match t.head() {
        Tm::Def(d) => Some(*d),
        _ => None,
    }
}

/// The number of parameters of a function type, and its result.
fn pi_arity(mut t: &Tm) -> (usize, &Tm) {
    let mut n = 0;
    while let Tm::Pi(_, _, _, _, b) = t {
        t = b;
        n += 1;
    }
    (n, t)
}

/// A Π-type after `n` of its parameters.
fn pi_peel(mut t: &Tm, n: usize) -> &Tm {
    for _ in 0..n {
        match t {
            Tm::Pi(_, _, _, _, b) => t = b,
            _ => break,
        }
    }
    t
}

fn head_is_con(t: &Tm) -> bool {
    matches!(t.head(), Tm::Con(_))
}

/// Check the body (a λ over the function's parameters) of `did`.
pub fn check_fn(e: &mut Elab, did: DefId, body: &Tm) {
    let mut u = U { e, did, binders: Vec::new(), reported: false, copied_by: Default::default(), captured: Default::default(), tail: true, ret: None, ret_own: false, ret_tm: None, result_holds: Default::default() };
    u.ret_own = u.e.fn_meta.get(&did).is_some_and(|m| m.result_own);
    // The function's own parameters; a lambda after them is a closure it
    // returns, which may be called any number of times (#658).
    let limit = u.e.fn_meta.get(&did).map_or(usize::MAX, |m| m.n_binders());
    let fty = u.e.g.defs[did.0 as usize].ty.clone();
    let mut pi = Some(&fty);
    let mut t = body;
    let mut n = 0;
    while let (Tm::Lam(x, m, _, b), true) = (t, n < limit) {
        let (ty, rest) = match pi {
            Some(Tm::Pi(_, _, _, a, r)) => (Some(BTy::Tm(a.clone())), Some(&**r)),
            _ => (None, None),
        };
        pi = rest;
        u.binders.push(Binder { name: x.to_string(), mult: *m, span: u.e.binder_span(x), lambda: false, resource: None, oneshot: None, ty });
        t = b;
        n += 1;
    }
    u.ret = pi.map(|r| u.e.eval_open(r));
    u.ret_tm = pi.cloned();
    let c = u.go(t);
    for lvl in (0..n).rev() {
        let mult = u.binders[lvl].mult;
        let k = count(&c, lvl);
        let bad = match mult {
            Mult::One => k != Count::One,
            Mult::Zero => k != Count::Zero,
            Mult::Many => false,
        };
        if bad && !u.reported {
            u.report(lvl, k, false);
        }
    }
}

fn head_is_meta(t: &Tm) -> bool {
    let h = t.head();
    matches!(h, Tm::Meta(_))
}
