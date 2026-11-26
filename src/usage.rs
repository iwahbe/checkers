//! Usage checking (QTT, §2 and §4): `own` values are used exactly once on
//! every path; `ghost` values never at runtime.

use crate::core::{CaseTm, DefId, Mult, Prim, Tm};
use crate::diag::Diagnostic;
use crate::source::Span;
use crate::elab::Elab;

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
    /// Where it is bound, if the elaborator recorded it (D172 d).
    span: Option<Span>,
    /// A lambda's parameter: `own` comes from the function type it is
    /// checked against, not from anything written.
    lambda: bool,
    /// A lambda parameter's resource type, when known (`File`).
    resource: Option<String>,
    /// Bound to a closure that uses this resource (or `own` value): the
    /// closure must be called exactly once (D171).
    oneshot: Option<String>,
}

struct U<'a> {
    e: &'a mut Elab,
    did: DefId,
    binders: Vec<Binder>,
    reported: bool,
    /// Binder level → a function it was passed to whose parameter isn't `own` (D45).
    /// The function each `own` binder is passed to as a parameter that isn't
    /// `own`, with its module.
    copied_by: std::collections::HashMap<usize, (String, String)>,
    /// The `own` binders a closure captures.
    captured: std::collections::BTreeSet<usize>,
}

type Counts = Vec<Count>;

fn add(a: &mut Counts, b: &Counts) {
    for (x, y) in a.iter_mut().zip(b) {
        *x = x.add(*y);
    }
}

impl U<'_> {
    fn zero(&self) -> Counts {
        vec![Count::Zero; self.binders.len()]
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
        if let Some(used) = b.oneshot.clone() {
            let d = match (mixed, c) {
                (true, _) => Diagnostic::error(
                    "E0402",
                    format!("`{name}` uses `{used}`, a resource, so it must be called exactly once, but `{fname}` calls it on some paths and not on others"),
                    span,
                ),
                (false, Count::Zero) => Diagnostic::error(
                    "E0401",
                    format!("`{name}` uses `{used}`, a resource, so it must be called exactly once, but `{fname}` never calls it"),
                    span,
                )
                .with_help(format!("call `{name}`, or pass it on to a parameter declared `own`")),
                _ => {
                    let d = Diagnostic::error(
                        "E0401",
                        format!("`{name}` uses `{used}`, a resource, so it must be called exactly once, but `{fname}` may call it more than once"),
                        span,
                    );
                    match self.copied_by.get(&lvl) {
                        Some((callee, _)) => d
                            .with_note(format!("`{name}` is passed to `{callee}`, whose parameter is not `own`, so `{callee}` may call it any number of times"))
                            .with_help(format!("mark that parameter of `{callee}` with `own` (as in `f~own (Unit -> a)`)")),
                        None => d.with_help("a closure that uses a resource is used up by its call"),
                    }
                }
            };
            self.e.err(d);
            self.reported = true;
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
                        // A cown can't hold a resource (D156 k).
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
        let c = counts[lvl];
        match self.binders[lvl].mult {
            Mult::One if c != Count::One => self.report(lvl, c, false),
            Mult::Zero if c != Count::Zero => self.report(lvl, c, false),
            _ => {}
        }
    }

    fn under(&mut self, name: &crate::core::Name, mult: Mult, body: &Tm, lambda: bool) -> Counts {
        let span = self.e.binder_span(name);
        let resource = if lambda { self.e.lam_resource(name) } else { None };
        self.binders.push(Binder { name: name.to_string(), mult, span, lambda, resource, oneshot: None });
        let c = self.go(body);
        self.close(&c);
        self.binders.pop();
        let mut c = c;
        c.pop();
        c
    }

    /// What a binder passed to `cown.new` or `actor.new` would be put in: a
    /// cown can't hold a resource (D156 k).
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
                let mut c = self.zero();
                let lvl = self.binders.len() - 1 - i;
                c[lvl] = Count::One;
                c
            }
            // An unsolved meta (an error was reported) uses nothing.
            Tm::App(..) if head_is_meta(t) => self.zero(),
            Tm::App(..) => self.app(t, false),
            Tm::Lam(x, m, _, b) => {
                let m = &if *m == Mult::One && self.e.lam_own_moot(x) { Mult::Many } else { *m };
                // A closure may run any number of times.
                let c = self.under(x, *m, b, true);
                for (lvl, n) in c.iter().enumerate() {
                    if *n != Count::Zero && self.binders[lvl].mult == Mult::One {
                        self.captured.insert(lvl);
                    }
                }
                c.into_iter().map(|c| c.scale(Mult::Many)).collect()
            }
            Tm::Let(x, m, _, v, b) => {
                // A tuple pattern binds each component (`$c0`, `$c1`, …) by
                // projecting the tuple: together they use it once, counted
                // at the first.
                let rest_of_tuple = x.starts_with("$c") && matches!(&**v, Tm::Proj(t, i, _) if *i > 0 && matches!(**t, Tm::Var(_)));
                let scale = if *m == Mult::Zero || rest_of_tuple { Mult::Zero } else { Mult::One };
                // A closure that uses a resource, bound by `let`: the
                // variable is used once instead (D171).
                if let (Some(used), false) = (self.oneshot_use(v), *m == Mult::Zero) {
                    let mut c = self.go_once(v);
                    self.binders.push(Binder { name: x.to_string(), mult: Mult::One, span: self.e.binder_span(x), lambda: false, resource: None, oneshot: Some(used) });
                    let cb = self.go(b);
                    self.close(&cb);
                    self.binders.pop();
                    let mut cb = cb;
                    cb.pop();
                    add(&mut c, &cb);
                    return c;
                }
                let mut c: Counts = self.go(v).into_iter().map(|c| c.scale(scale)).collect();
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
                    let cx: Counts = self.go(x).into_iter().map(|c| c.scale(if m == Mult::Zero { Mult::Zero } else { Mult::One })).collect();
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
                let (head, args) = t.spine();
                let n = args.len();
                match head {
                    // A constructor stores its arguments.
                    Tm::Con(_) => args.into_iter().for_each(|x| self.carried_into(x, depth, out)),
                    // A saturated call carries its arguments only if its result may hold a resource.
                    Tm::Def(d) => {
                        let ty = &self.e.g.defs[d.0 as usize].ty;
                        let (arity, result) = pi_arity(ty);
                        if n < arity || self.e.type_linear(result) {
                            all(t, depth, out);
                        }
                    }
                    _ => all(t, depth, out),
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
    /// makes, if it is a partial application, exactly once.
    fn app(&mut self, t: &Tm, once: bool) -> Counts {
        let Tm::App(f, a, _, m) = t else { return self.go(t) };
        // A lambda called where it is made runs once (D171).
        let mut c = match &**f {
            Tm::Lam(..) => self.lam_once(f),
            // The rest of this call: what it partly applies is decided at the top.
            Tm::App(..) => self.app(f, true),
            _ => self.go(f),
        };
        // A constructor stores its argument: one use, like a saturated `ConApp`.
        let m = if *m != Mult::Zero && head_is_con(f) { Mult::One } else { *m };
        // A lambda passed to an `own` parameter is called once (D171).
        let used = if m == Mult::One { self.go_once(a) } else { self.go(a) };
        // Arguments are evaluated once, before the call: only what can be
        // part of the argument's value is used as often as the parameter
        // allows; a use inside it (`f` in `g (close f)`) happens once.
        let carried = self.carried(a);
        if m == Mult::Many {
            if let Some(callee) = head_def(f).map(|d| {
                let d = &self.e.g.defs[d.0 as usize];
                (d.name.to_string(), d.module.to_string())
            }) {
                for (lvl, c) in used.iter().enumerate() {
                    if *c != Count::Zero && self.binders[lvl].mult == Mult::One && carried.contains(&lvl) {
                        self.copied_by.entry(lvl).or_insert_with(|| callee.clone());
                    }
                }
            }
        }
        // An erased argument (a type, a ghost value) uses nothing at all,
        // even what it only computes from (`a` in `wrap s a`).
        let ca: Counts = used
            .into_iter()
            .enumerate()
            .map(|(lvl, x)| if m == Mult::Zero || carried.contains(&lvl) { x.scale(m) } else { x })
            .collect();
        add(&mut c, &ca);
        // A partial application holding a resource is a closure that
        // uses it: unless this is a place that calls it once, it may
        // be called any number of times (D171).
        if !once && self.partial_use(t).is_some() {
            for (lvl, x) in c.iter_mut().enumerate() {
                if *x != Count::Zero && self.binders[lvl].mult == Mult::One {
                    *x = Count::Many;
                    self.captured.insert(lvl);
                }
            }
        }
        c
    }

    /// `t` where what it makes is called exactly once: a lambda, or a
    /// partial application, holding a resource (D171).
    fn go_once(&mut self, t: &Tm) -> Counts {
        match t {
            Tm::Lam(..) => self.lam_once(t),
            Tm::App(..) if !head_is_meta(t) => self.app(t, true),
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
    /// name of one it uses: such a closure must be called exactly once (D171).
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

    fn lam_once(&mut self, t: &Tm) -> Counts {
        match t {
            Tm::Lam(x, m, _, b) => {
                let m = &if *m == Mult::One && self.e.lam_own_moot(x) { Mult::Many } else { *m };
                self.binders.push(Binder { name: x.to_string(), mult: *m, span: self.e.binder_span(x), lambda: true, resource: self.e.lam_resource(x), oneshot: None });
                let c = self.lam_once(b);
                self.close(&c);
                self.binders.pop();
                let mut c = c;
                c.pop();
                c
            }
            other => self.go(other),
        }
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
            // (D173): used any number of times here, as if exactly once.
            let moot: Vec<usize> = match scrut {
                Some(s) => (0..start)
                    .filter(|l| self.binders[*l].mult == Mult::One && self.e.moot_in_arm.contains(&(self.did, s, *con, *l)))
                    .collect(),
                None => Vec::new(),
            };
            for l in &moot {
                self.binders[*l].mult = Mult::Many;
            }
            for k in 0..*n {
                self.binders.push(Binder { name: format!("$field{k}"), mult: Mult::Many, span: None, lambda: false, resource: None, oneshot: None });
            }
            let mut r = self.go(body);
            self.binders.truncate(start);
            r.truncate(start);
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
        for lvl in 0..out.len() {
            let mult = self.binders[lvl].mult;
            // An arm where it holds no resource doesn't constrain it (D173);
            // if none does, it counts as used once.
            let all: Vec<Count> =
                results.iter().zip(&moots).filter(|(_, m)| !m.contains(&lvl)).map(|(r, _)| r[lvl]).collect();
            let Some(first) = all.first().copied() else {
                out[lvl] = Count::One;
                continue;
            };
            if mult == Mult::One && all.iter().any(|x| *x != first) && !self.reported {
                let has_one = all.contains(&Count::One);
                let has_zero = all.contains(&Count::Zero);
                if has_one && has_zero {
                    self.report(lvl, Count::One, true);
                }
            }
            out[lvl] = all.iter().copied().fold(Count::Zero, |a, b| match (a, b) {
                (Count::Many, _) | (_, Count::Many) => Count::Many,
                (Count::One, _) | (_, Count::One) => Count::One,
                _ => Count::Zero,
            });
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

fn head_is_con(t: &Tm) -> bool {
    matches!(t.head(), Tm::Con(_))
}

/// Check the body (a λ over the function's parameters) of `did`.
pub fn check_fn(e: &mut Elab, did: DefId, body: &Tm) {
    let mut u = U { e, did, binders: Vec::new(), reported: false, copied_by: Default::default(), captured: Default::default() };
    // The function's own parameters; a lambda after them is a closure it
    // returns, which may be called any number of times (D171).
    let limit = u.e.fn_meta.get(&did).map_or(usize::MAX, |m| m.n_binders());
    let mut t = body;
    let mut n = 0;
    while let (Tm::Lam(x, m, _, b), true) = (t, n < limit) {
        u.binders.push(Binder { name: x.to_string(), mult: *m, span: u.e.binder_span(x), lambda: false, resource: None, oneshot: None });
        t = b;
        n += 1;
    }
    let c = u.go(t);
    for lvl in (0..n).rev() {
        let mult = u.binders[lvl].mult;
        let k = c[lvl];
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
