//! Usage checking (QTT, §2 and §4): `own` values are used exactly once on
//! every path; `ghost` values never at runtime.

use crate::core::{CaseTm, DefId, Mult, Prim, Tm};
use crate::diag::Diagnostic;
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
}

struct U<'a> {
    e: &'a mut Elab,
    did: DefId,
    binders: Vec<Binder>,
    reported: bool,
    /// Binder level → a function it was passed to whose parameter isn't `own` (D45).
    copied_by: std::collections::HashMap<usize, String>,
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
        let meta = self.e.fn_meta.get(&self.did).cloned().unwrap_or_default();
        let resource = self.e.resource_vars.get(&(self.did, b.name.clone())).cloned();
        let span = match &resource {
            Some((s, _)) => *s,
            None => meta.params.iter().find(|p| p.0 == b.name).map(|p| p.2).unwrap_or(meta.span),
        };
        let fname = meta.name.clone();
        let name = b.name.clone();
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
                .with_help("close it, or pass it on"),
                _ => {
                    let d = Diagnostic::error(
                        "E0401",
                        format!("`{name}` holds a resource (`{ty}`), so it must be used exactly once, but `{fname}` may use it more than once"),
                        span,
                    );
                    match self.copied_by.get(&lvl) {
                        Some(callee) => d
                            .with_note(format!("`{name}` is passed to `{callee}`, whose parameter is not `own`, so `{callee}` may copy or drop it"))
                            .with_help(format!("mark that parameter of `{callee}` with `own` (as in `x~own a`) so it can take a resource")),
                        None => d.with_help("a resource can't be copied; thread it with `<-` so each use gets the new one"),
                    }
                }
            };
            self.e.err(d);
            self.reported = true;
            return;
        }
        let d = match (b.mult, mixed, c) {
            (Mult::Zero, _, _) => Diagnostic::error(
                "E0403",
                format!("`{name}` is `ghost`: it may only appear in types and constraints, but `{fname}` uses it at runtime"),
                span,
            )
            .with_help("remove `ghost` if the value is needed at runtime"),
            (_, true, _) => Diagnostic::error(
                "E0402",
                format!("`{name}` is `own`, but `{fname}` uses it on some paths and not on others"),
                span,
            )
            .with_help("an `own` value must be used exactly once on every path"),
            (_, false, Count::Zero) => Diagnostic::error(
                "E0401",
                format!("`{name}` is `own`, so it must be used exactly once, but `{fname}` never uses it"),
                span,
            )
            .with_help("`own` promises a single use, so the argument may be a resource that must not be dropped; use it, or remove `own`"),
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

    fn under(&mut self, name: &str, mult: Mult, body: &Tm) -> Counts {
        self.binders.push(Binder { name: name.to_string(), mult });
        let c = self.go(body);
        self.close(&c);
        self.binders.pop();
        let mut c = c;
        c.pop();
        c
    }

    fn go(&mut self, t: &Tm) -> Counts {
        match t {
            Tm::Var(i) => {
                let mut c = self.zero();
                let lvl = self.binders.len() - 1 - i;
                c[lvl] = Count::One;
                c
            }
            Tm::App(f, a, _, m) => {
                let mut c = self.go(f);
                // A constructor stores its argument: one use, like a saturated `ConApp`.
                let m = if *m != Mult::Zero && head_is_con(f) { Mult::One } else { *m };
                let used = self.go(a);
                // Arguments are evaluated once, before the call: only what can be
                // part of the argument's value is used as often as the parameter
                // allows; a use inside it (`f` in `g (close f)`) happens once.
                let carried = self.carried(a);
                if m == Mult::Many {
                    if let Some(callee) = head_def(f).map(|d| self.e.g.defs[d.0 as usize].name.to_string()) {
                        for (lvl, c) in used.iter().enumerate() {
                            if *c != Count::Zero && self.binders[lvl].mult == Mult::One && carried.contains(&lvl) {
                                self.copied_by.entry(lvl).or_insert_with(|| callee.clone());
                            }
                        }
                    }
                }
                let ca: Counts =
                    used.into_iter().enumerate().map(|(lvl, x)| if carried.contains(&lvl) { x.scale(m) } else { x }).collect();
                add(&mut c, &ca);
                c
            }
            Tm::Lam(x, m, _, b) => {
                // A closure may run any number of times.
                self.under(x, *m, b).into_iter().map(|c| c.scale(Mult::Many)).collect()
            }
            Tm::Let(x, m, _, v, b) => {
                let mut c: Counts = self.go(v).into_iter().map(|c| c.scale(if *m == Mult::Zero { Mult::Zero } else { Mult::One })).collect();
                let cb = self.under(x, *m, b);
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
                for x in v {
                    // Behaviour bodies run once: a resource may move into them.
                    let cx = match (p, x) {
                        (Prim::Fork | Prim::Join | Prim::When, Tm::Lam(..)) => self.lam_once(x),
                        _ => self.go(x),
                    };
                    add(&mut c, &cx);
                }
                c
            }
            Tm::Proj(x, _) | Tm::Field(x, _, _) => self.go(x),
            Tm::Case(s, c) => {
                let mut cs = self.go(s);
                let cb = self.case(c);
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
            Tm::Var(_) | Tm::Lit(_) | Tm::Def(_) | Tm::Con(_) | Tm::Univ(_) | Tm::TyCon(_) | Tm::Error => {}
            Tm::Tuple(v) | Tm::ConApp(_, v) => v.iter().for_each(|x| self.carried_into(x, depth, out)),
            Tm::Proj(x, _) | Tm::Field(x, _, _) => self.carried_into(x, depth, out),
            Tm::Let(_, _, _, v, b) => {
                self.carried_into(v, depth, out);
                self.carried_into(b, depth + 1, out);
            }
            Tm::App(..) => {
                let (head, n) = spine(t);
                match head {
                    // A constructor stores its arguments.
                    Tm::Con(_) => app_args(t).into_iter().for_each(|x| self.carried_into(x, depth, out)),
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
                | Prim::Len
                | Prim::Format,
                _,
            ) => {}
            // A closure, a match, an element, a builtin: everything they mention.
            _ => all(t, depth, out),
        }
    }

    fn lam_once(&mut self, t: &Tm) -> Counts {
        match t {
            Tm::Lam(x, m, _, b) => {
                self.binders.push(Binder { name: x.to_string(), mult: *m });
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

    fn case(&mut self, c: &CaseTm) -> Counts {
        let mut results: Vec<Counts> = Vec::new();
        for (_, n, body) in &c.branches {
            if matches!(body, Tm::Error) {
                continue;
            }
            let start = self.binders.len();
            for k in 0..*n {
                self.binders.push(Binder { name: format!("$field{k}"), mult: Mult::Many });
            }
            let mut r = self.go(body);
            self.binders.truncate(start);
            r.truncate(start);
            results.push(r);
        }
        for (_, body) in &c.lits {
            if !matches!(body, Tm::Error) {
                results.push(self.go(body));
            }
        }
        if let Some(d) = c.default.as_ref().filter(|d| !matches!(d, Tm::Error)) {
            results.push(self.go(d));
        }
        // Branches without code (errors already reported) don't constrain usage.
        let mut out = self.zero();
        let Some(first) = results.first() else { return out };
        for lvl in 0..out.len() {
            let mult = self.binders[lvl].mult;
            let all: Vec<Count> = results.iter().map(|r| r[lvl]).collect();
            if mult == Mult::One && all.iter().any(|x| *x != first[lvl]) && !self.reported {
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

fn head_def(mut t: &Tm) -> Option<DefId> {
    while let Tm::App(f, ..) = t {
        t = f;
    }
    match t {
        Tm::Def(d) => Some(*d),
        _ => None,
    }
}

/// The head of an application and how many arguments it has.
fn spine(mut t: &Tm) -> (&Tm, usize) {
    let mut n = 0;
    while let Tm::App(f, ..) = t {
        t = f;
        n += 1;
    }
    (t, n)
}

fn app_args(mut t: &Tm) -> Vec<&Tm> {
    let mut v = Vec::new();
    while let Tm::App(f, a, ..) = t {
        v.push(&**a);
        t = f;
    }
    v.reverse();
    v
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

fn head_is_con(mut t: &Tm) -> bool {
    while let Tm::App(f, ..) = t {
        t = f;
    }
    matches!(t, Tm::Con(_))
}

/// Check the body (a λ over the function's parameters) of `did`.
pub fn check_fn(e: &mut Elab, did: DefId, body: &Tm) {
    let mut u = U { e, did, binders: Vec::new(), reported: false, copied_by: Default::default() };
    let mut t = body;
    let mut n = 0;
    while let Tm::Lam(x, m, _, b) = t {
        u.binders.push(Binder { name: x.to_string(), mult: *m });
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
