//! Usage checking (QTT, §2 and §4): `own` values are used exactly once on
//! every path; `ghost` values never at runtime.

use crate::core::{CaseTm, DefId, Mult, Prim, Tm};
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
}

struct U<'a> {
    e: &'a mut Elab,
    did: DefId,
    binders: Vec<Binder>,
    reported: bool,
    /// Binder level → a function it was passed to whose parameter isn't `own` (#545).
    /// The function each `own` binder is passed to as a parameter that isn't
    /// `own`, with its module.
    copied_by: std::collections::HashMap<usize, (String, String)>,
    /// Whether a definition's result may hold one of its arguments: asked
    /// at each call `carried` looks through.
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
        if let (Some((_, ty)), Mult::One) = (&resource, b.mult) {
            // A function used exactly once (`own (Unit -> Unit)`, §8.4): a
            // closure that holds a resource.
            let func = crate::core::plain(ty).starts_with("own (");
            let generic = self.e.own_generic.contains(&(self.did, name.clone()));
            let (held, what, verb, verbs) = if func {
                (format!("`{name}` is `{ty}`"), format!("`{name}` is `{ty}`, a function to call exactly once"), "call", "calls")
            } else if generic {
                (
                    format!("`{name}` (`{ty}`) may hold a resource"),
                    format!("`{name}` (`{ty}`) may hold a resource, since an `own` parameter's type may be one, so it must be used exactly once"),
                    "use",
                    "uses",
                )
            } else {
                (format!("`{name}` holds a resource (`{ty}`)"), format!("`{name}` holds a resource (`{ty}`), so it must be used exactly once"), "use", "uses")
            };
            let d = match (mixed, c) {
                (true, _) => {
                    Diagnostic::error("E0402", format!("{held}, but `{fname}` {verbs} it on some paths and not on others"), span).with_help(if func {
                        "call it exactly once on every path"
                    } else {
                        "a resource must be used exactly once on every path, e.g. closed in every branch"
                    })
                }
                (false, Count::Zero) => Diagnostic::error("E0401", format!("{what}, but `{fname}` never {verbs} it"), span).with_help(
                    if func {
                        "call it, or pass it on"
                    } else if crate::core::plain(ty).contains("own (") {
                        "call the function it holds, or pass it on"
                    } else if crate::core::plain(ty).starts_with("Future ") {
                        "join it: a future of a resource is one too, joined exactly once"
                    } else {
                        "close it, or pass it on"
                    },
                ),
                _ => {
                    let d = Diagnostic::error("E0401", format!("{what}, but `{fname}` may {verb} it more than once"), span);
                    match self.copied_by.get(&lvl) {
                        // A cown can't hold a resource (#643 k).
                        Some((_, module)) if self.cown_target(lvl).is_some() => {
                            let what = self.cown_target(lvl).unwrap_or_default();
                            let short = module.trim_start_matches("std.");
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
                        Some((callee, _)) => d
                            .with_note(format!("`{name}` is passed to `{callee}`, whose parameter is not `own`, so `{callee}` may copy or drop it"))
                            .with_help(format!("mark that parameter of `{callee}` with `own` (as in `x~own a`) so it can take a resource")),
                        None if func => d.with_help("a function of type `own (…)` is used up by its call"),
                        None if generic => d.with_help("a value built from an `own` value is used up by its use, as the `own` value is"),
                        None if crate::core::plain(ty).contains("own (") => {
                            d.with_help("a value holding a function of type `own (…)` is used up by its use, as the function is by its call")
                        }
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
            .with_notes(self.copied_by.get(&lvl).map(|(callee, _)| {
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
                span,
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

    fn under(&mut self, name: &crate::core::Name, mult: Mult, body: &Tm, lambda: bool) -> Counts {
        let span = self.e.binder_span(name);
        let resource = if lambda { self.e.lam_resource(name) } else { None };
        self.binders.push(Binder { name: name.to_string(), mult, span, lambda, resource });
        let c = self.go(body);
        self.close(&c);
        self.binders.pop();
        let mut c = c;
        c.remove(&self.binders.len());
        c
    }

    /// What a binder passed to `cown.new` or `actor.new` would be put in: a
    /// cown can't hold a resource (#643 k).
    fn cown_target(&self, lvl: usize) -> Option<String> {
        match self.copied_by.get(&lvl).map(|(c, m)| (c.as_str(), m.as_str())) {
            Some(("new", "std.cown")) => Some("a cown".into()),
            Some(("new", "std.actor")) => Some("an actor's state".into()),
            _ => None,
        }
    }

    fn go(&mut self, t: &Tm) -> Counts {
        match t {
            Tm::Var(i) => {
                let lvl = self.binders.len() - 1 - i;
                Counts::from([(lvl, Count::One)])
            }
            // An unsolved meta (an error was reported) uses nothing.
            Tm::App(..) if head_is_meta(t) => self.zero(),
            Tm::App(..) => self.app(t),
            Tm::Lam(x, m, _, b) => {
                let m = &if *m == Mult::One && self.e.lam_own_moot(x) { Mult::Many } else { *m };
                // A closure that holds what must be used exactly once is
                // itself, by its type (§8.4): what it captures is used once,
                // when it is. One that holds nothing of the kind may run any
                // number of times, which changes nothing for what it uses.
                self.under(x, *m, b, true)
            }
            Tm::Let(x, m, _, v, b) => {
                // A tuple pattern binds each component (`$c0`, `$c1`, …) by
                // projecting the tuple: together they use it once, counted
                // at the first.
                let rest_of_tuple = x.starts_with("$c") && matches!(&**v, Tm::Proj(t, i, _) if *i > 0 && matches!(**t, Tm::Var(_)));
                let scale = if *m == Mult::Zero || rest_of_tuple { Mult::Zero } else { Mult::One };
                let mut c = scaled(self.go(v), scale);
                let cb = self.under(x, *m, b, false);
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
                    let cx = self.go(x);
                    add(&mut c, &cx);
                }
                c
            }
            Tm::Proj(x, _, _) | Tm::Field(x, _, _) => self.go(x),
            Tm::Case(s, c) => {
                let mut cs = self.go(s);
                let scrut = match &**s {
                    Tm::Var(i) => Some(self.binders.len() - 1 - i),
                    _ => None,
                };
                let cb = self.case(c, scrut);
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
    fn carried(&self, t: &Tm) -> std::collections::BTreeSet<usize> {
        let mut out = std::collections::BTreeSet::new();
        self.carried_into(t, 0, &mut out);
        out
    }

    /// `depth`: binders `t` is under that aren't in `self.binders`.
    fn carried_into(&self, t: &Tm, depth: usize, out: &mut std::collections::BTreeSet<usize>) {
        let all = |t: &Tm, depth: usize, out: &mut std::collections::BTreeSet<usize>| {
            let mut fv = std::collections::BTreeSet::new();
            crate::core::free_vars(t, depth, &mut fv);
            for i in fv {
                if let Some(l) = self.binders.len().checked_sub(1 + i) {
                    out.insert(l);
                }
            }
        };
        match t {
            Tm::Var(i) if *i >= depth => {
                if let Some(l) = self.binders.len().checked_sub(1 + (i - depth)) {
                    out.insert(l);
                }
            }
            Tm::Var(_) | Tm::Lit(_) | Tm::Known(_) | Tm::Def(_) | Tm::Con(_) | Tm::Univ(_) | Tm::TyCon(_) | Tm::Error => {}
            Tm::Tuple(v) | Tm::ConApp(_, v) => v.iter().for_each(|x| self.carried_into(x, depth, out)),
            Tm::Proj(x, _, _) | Tm::Field(x, _, _) => self.carried_into(x, depth, out),
            // A call with effects is the call (§7.1).
            Tm::PrimApp(Prim::Effect(_), v) => v.iter().for_each(|x| self.carried_into(x, depth, out)),
            Tm::Let(_, _, _, v, b) => {
                self.carried_into(v, depth, out);
                self.carried_into(b, depth + 1, out);
            }
            Tm::App(..) => {
                // Erased arguments (types, `ghost` values) carry nothing.
                let mut head = t;
                let mut args = Vec::new();
                let mut n = 0;
                while let Tm::App(f, a, _, m) = head {
                    if *m != Mult::Zero {
                        args.push(&**a);
                    }
                    n += 1;
                    head = f;
                }
                match head {
                    // A constructor stores its arguments.
                    Tm::Con(_) => args.into_iter().for_each(|x| self.carried_into(x, depth, out)),
                    // A partial application holds its arguments; a saturated
                    // call carries them only if its result may hold one.
                    Tm::Def(d) => {
                        let ty = &self.e.g.defs[d.0 as usize].ty;
                        // A result that is a function adds to the Π-type's
                        // binders: a definition's own are its parameters.
                        let arity = self.e.fn_meta.get(d).map_or_else(|| pi_arity(ty).0, |m| m.n_binders());
                        let result = pi_peel(ty, arity);
                        let holds = || *self.result_holds.borrow_mut().entry(*d).or_insert_with(|| self.e.may_hold_linear(&self.e.eval_open(result)));
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

    /// An application.
    fn app(&mut self, t: &Tm) -> Counts {
        let Tm::App(f, a, _, m) = t else { return self.go(t) };
        let mut c = self.go(f);
        // A constructor stores its argument: one use, like a saturated `ConApp`.
        let m = if *m != Mult::Zero && head_is_con(f) { Mult::One } else { *m };
        let used = self.go(a);
        // Arguments are evaluated once, before the call: only what can be
        // part of the argument's value is used as often as the parameter
        // allows; a use inside it (`f` in `g (close f)`) happens once.
        let carried = self.carried(a);
        if m == Mult::Many {
            if let Some(callee) = head_def(f).map(|d| {
                let d = &self.e.g.defs[d.0 as usize];
                (d.name.to_string(), d.module.to_string())
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
        c
    }

    fn case(&mut self, c: &CaseTm, scrut: Option<usize>) -> Counts {
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
            for k in 0..*n {
                self.binders.push(Binder { name: format!("$field{k}"), mult: Mult::Many, span: None, lambda: false, resource: None });
            }
            let mut r = self.go(body);
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
                results.push(self.go(body));
                moots.push(Vec::new());
            }
        }
        if let Some(d) = c.default.as_ref().filter(|d| !matches!(d, Tm::Error)) {
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
    while let Tm::Pi(_, _, _, _, b, _) = t {
        t = b;
        n += 1;
    }
    (n, t)
}

/// A Π-type after `n` of its parameters.
fn pi_peel(mut t: &Tm, n: usize) -> &Tm {
    for _ in 0..n {
        match t {
            Tm::Pi(_, _, _, _, b, _) => t = b,
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
    let mut u = U { e, did, binders: Vec::new(), reported: false, copied_by: Default::default(), result_holds: Default::default() };
    // The function's own parameters; a lambda after them is a closure it
    // returns, which may be called any number of times (#658).
    let limit = u.e.fn_meta.get(&did).map_or(usize::MAX, |m| m.n_binders());
    let mut t = body;
    let mut n = 0;
    while let (Tm::Lam(x, m, _, b), true) = (t, n < limit) {
        u.binders.push(Binder { name: x.to_string(), mult: *m, span: u.e.binder_span(x), lambda: false, resource: None });
        t = b;
        n += 1;
    }
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
