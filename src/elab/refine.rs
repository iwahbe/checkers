//! Refinements inside types (D71, D82–D87, §7.1, §7.5).
//!
//! A refinement alias (`type Small = n~Nat, n < 10`) is the same type as its
//! base for unification, so on its own `List Nat` would pass for
//! `List Small`. An inline refinement (`(n~Nat, n < 10)`) and a refined
//! function type (`(x~Int -> y~Int, x >= 5, y >= 0)`) are anonymous aliases
//! (`elab_refine`). The rules that keep them meaningful:
//!
//! - A value checked against a refinement alias gets the alias's predicates
//!   as obligations (`refined_obligation`), unless the call or constructor
//!   it is an argument of already checks them (a parameter or field whose
//!   declared type is the alias).
//! - After unification, the expected and found types are compared by
//!   variance (`refined_mismatch`): where both have a refinement, one must
//!   imply the other, an obligation for any value (D83, D85); a refinement
//!   may be forgotten (`List Small` as `List Nat`) but never gained (E0262).
//! - A function with a specification, used as a value or partially applied,
//!   gets a refined function type (`refined_fn_type`, D85, D86).

use super::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Variance {
    Co,
    Contra,
    Inv,
}

impl Variance {
    fn then(self, inner: Variance) -> Variance {
        match (self, inner) {
            (Variance::Inv, _) | (_, Variance::Inv) => Variance::Inv,
            (Variance::Co, v) => v,
            (Variance::Contra, Variance::Co) => Variance::Contra,
            (Variance::Contra, Variance::Contra) => Variance::Co,
        }
    }
}

/// Where a refinement would be gained: the alias expected, the type found
/// in its place, and whether the position is invariant (a cown's contents).
pub struct Gained {
    pub expected: Val,
    pub found: Val,
    pub variance: Variance,
    /// What made the position contravariant or invariant: a function's
    /// argument, or a parameter of a type constructor.
    pub via: Via,
    /// The context `expected` and `found` live in: inside a function
    /// type's result, its parameter is bound (`sr~Option s, shorter sr ys`
    /// mentions `ys`), so they are shown there, not at the comparison's.
    pub cx: Cx,
}

/// Where a comparison of refinements was asked for, for its obligations.
pub struct Walk {
    span: Span,
    value: String,
    callee: Option<String>,
    /// What its obligations are for, if not a weakened refinement.
    kind: Option<ObKind>,
}

#[derive(Clone, Copy)]
pub enum Via {
    Nothing,
    Fn,
    Ty(TyId),
}

impl Elab {
    /// `v` as a refinement alias applied to its arguments (metas solved,
    /// nothing unfolded).
    pub fn refined_alias(&self, v: &Val) -> Option<(DefId, Vec<Val>)> {
        match force_meta(&self.g, v.clone()) {
            Val::Neutral(Head::Def(d), sp) if self.alias_preds.contains_key(&d) => {
                let mut args = Vec::new();
                for e in sp.iter() {
                    match e {
                        Elim::App(a, _) => args.push(a.clone()),
                        _ => return None,
                    }
                }
                Some((d, args))
            }
            _ => None,
        }
    }

    /// Is `v` a refinement alias written directly (not reached through a meta)?
    pub fn is_direct_alias(&self, v: &Val) -> bool {
        matches!(v, Val::Neutral(Head::Def(d), _) if self.alias_preds.contains_key(d))
    }

    /// Does `v` mention a refinement alias anywhere a value could be checked
    /// against it?
    pub fn has_refined(&self, cx: &Cx, v: &Val, depth: usize) -> bool {
        if depth > 8 {
            return false;
        }
        if self.refined_alias(v).is_some() {
            return true;
        }
        match self.peel(v) {
            Val::TyCon(_, args) => args.iter().any(|a| self.has_refined(cx, a, depth + 1)),
            Val::TupleTy(ts) => ts.iter().any(|a| self.has_refined(cx, a, depth + 1)),
            Val::Pi(_, _, _, a, c) => {
                self.has_refined(cx, &a, depth + 1)
                    || self.has_refined(cx, &apply_closure(&self.g, &c, Val::var(cx.lvl() + depth)), depth + 1)
            }
            _ => false,
        }
    }

    /// Solve metas and unfold plain (unrefined) aliases, keeping refinement
    /// aliases.
    pub(super) fn peel(&self, v: &Val) -> Val {
        let mut v = force_meta(&self.g, v.clone());
        for _ in 0..32 {
            if self.refined_alias(&v).is_some() {
                return v;
            }
            match unfold(&self.g, &v) {
                Some(u) => v = force_meta(&self.g, u),
                None => return v,
            }
        }
        v
    }

    /// A refinement alias's base, with all aliases unfolded at the head.
    fn base(&self, v: &Val) -> Val {
        self.force(v)
    }

    /// The variance of each parameter of a type constructor: from its
    /// marks for an abstract type (D16), otherwise covariant where the
    /// parameter is strictly positive and invariant elsewhere.
    pub fn variance(&self, t: TyId) -> Vec<Variance> {
        let ti = &self.g.tys[t.0 as usize];
        (0..ti.params.len())
            .map(|j| {
                if ti.positive.get(j).copied().unwrap_or(false) {
                    Variance::Co
                } else if ti.negative.get(j).copied().unwrap_or(false) {
                    Variance::Contra
                } else {
                    Variance::Inv
                }
            })
            .collect()
    }

    /// Compare an expected and a found type that unify (D71, D83, D85).
    /// Where both have a refinement in the same place, the found one must
    /// imply the expected one (flipped in a contravariant place): an
    /// obligation for any value. Where only the one that must imply has
    /// none, it is gained: the first such place is returned (E0262), except
    /// for a function's parameter, where an unrefined expectation is the
    /// weakest and gives an obligation too.
    /// Is `sup` a refinement of `sub`'s alias, through the aliases it is
    /// defined with (`Small = n~Nat, …` refines `Nat`)?
    pub fn refines(&self, sup: &Val, sub: &Val) -> bool {
        let Some((d, _)) = self.refined_alias(sub) else { return false };
        let mut v = force_meta(&self.g, sup.clone());
        for _ in 0..64 {
            match crate::core::unfold(&self.g, &v) {
                Some(u) => v = force_meta(&self.g, u),
                None => return false,
            }
            if self.refined_alias(&v).is_some_and(|(e, _)| e == d) {
                return true;
            }
        }
        false
    }

    pub fn refined_mismatch(&mut self, cx: &Cx, expected: &Val, found: &Val, span: Span) -> Option<Gained> {
        // The same type on both sides gains nothing; most types have no
        // refinement inside them. Either way: nothing to walk, and no need
        // to copy the context (most of the time this took).
        if self.same_type(expected, found) {
            return None;
        }
        if !self.refined_inside(expected, cx.lvl(), 0) && !self.refined_inside(found, cx.lvl(), 0) {
            return None;
        }
        let mut cx2 = cx.clone();
        let text = self.src_text(span);
        let value = match text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
            Some(inner) if !inner.contains(['(', ')']) => inner.to_string(),
            _ => text,
        };
        let w = Walk { span, value, callee: self.arg_of.clone(), kind: None };
        self.gain(&mut cx2, expected, found, Variance::Co, Via::Nothing, false, 0, &w)
    }

    /// Whether every `found` is an `expected`, two types that unify, as
    /// `refined_mismatch` compares them: true with an obligation of `kind`
    /// at `span` for each refinement to imply, false where one would be
    /// gained.
    pub fn refined_implies(&mut self, cx: &Cx, expected: &Val, found: &Val, span: Span, kind: ObKind) -> bool {
        if self.same_type(expected, found) {
            return true;
        }
        if unify(&self.g, cx.lvl(), expected, found).is_err() {
            return false;
        }
        let mut cx2 = cx.clone();
        let w = Walk { span, value: String::new(), callee: None, kind: Some(kind) };
        // From depth 1: a refinement at the top is compared too.
        self.gain(&mut cx2, expected, found, Variance::Co, Via::Nothing, false, 1, &w).is_none()
    }

    /// Whether every `found` is an `expected` below their tops (a
    /// refinement at the top is the caller's to compare), as
    /// `refined_implies` compares them: obligations of `kind` at `span`
    /// for each refinement to imply, and the place where one would be
    /// gained, if any.
    pub fn refined_implies_inside(&mut self, cx: &Cx, expected: &Val, found: &Val, span: Span, kind: ObKind) -> Option<Gained> {
        if self.same_type(expected, found) || (!self.refined_inside(expected, cx.lvl(), 0) && !self.refined_inside(found, cx.lvl(), 0)) {
            return None;
        }
        let mut cx2 = cx.clone();
        let w = Walk { span, value: String::new(), callee: None, kind: Some(kind) };
        self.gain(&mut cx2, expected, found, Variance::Co, Via::Nothing, false, 0, &w)
    }

    /// The same type, structurally (without unfolding): false if unsure.
    fn same_type(&self, a: &Val, b: &Val) -> bool {
        if matches!(a, Val::Neutral(Head::Meta(_), _)) || matches!(b, Val::Neutral(Head::Meta(_), _)) {
            let (a, b) = (force_meta(&self.g, a.clone()), force_meta(&self.g, b.clone()));
            if matches!(a, Val::Neutral(Head::Meta(_), _)) || matches!(b, Val::Neutral(Head::Meta(_), _)) {
                return matches!((&a, &b), (Val::Neutral(Head::Meta(x), s1), Val::Neutral(Head::Meta(y), s2)) if x == y && s1.is_empty() && s2.is_empty());
            }
            return self.same_type(&a, &b);
        }
        match (a, b) {
            (Val::TyCon(t1, x1), Val::TyCon(t2, x2)) => t1 == t2 && x1.len() == x2.len() && x1.iter().zip(x2).all(|(x, y)| self.same_type(x, y)),
            (Val::TupleTy(x1), Val::TupleTy(x2)) => x1.len() == x2.len() && x1.iter().zip(x2).all(|(x, y)| self.same_type(x, y)),
            (Val::Univ(u1), Val::Univ(u2)) => u1 == u2,
            (Val::Neutral(h1, s1), Val::Neutral(h2, s2)) => {
                let heads = match (h1, h2) {
                    (Head::Var(x), Head::Var(y)) => x == y,
                    (Head::Meta(x), Head::Meta(y)) => x == y,
                    (Head::Def(x), Head::Def(y)) => x == y,
                    _ => false,
                };
                heads
                    && s1.len() == s2.len()
                    && s1.iter().zip(s2.iter()).all(|(e1, e2)| match (e1, e2) {
                        (Elim::App(x, i), Elim::App(y, j)) => i == j && self.same_type(x, y),
                        (Elim::Proj(i, a), Elim::Proj(j, b)) => i == j && a == b,
                        (Elim::Field(c, i), Elim::Field(d, j)) => c == d && i == j,
                        _ => false,
                    })
            }
            _ => false,
        }
    }

    /// Whether `gain` could find something in `v`: a refinement alias
    /// below the top (`depth > 0`), as `gain` walks it.
    fn refined_inside(&self, v: &Val, lvl: usize, depth: usize) -> bool {
        if depth > 16 {
            return false;
        }
        let p = self.peel(v);
        if depth > 0 && self.refined_alias(&p).is_some() {
            return true;
        }
        match self.base(&p) {
            Val::TyCon(_, args) => args.iter().any(|a| self.refined_inside(a, lvl, depth + 1)),
            Val::TupleTy(xs) => xs.iter().any(|a| self.refined_inside(a, lvl, depth + 1)),
            Val::Pi(_, _, _, a, c) => {
                self.refined_inside(&a, lvl, depth + 1) || self.refined_inside(&apply_closure(&self.g, &c, Val::var(lvl)), lvl + 1, depth + 1)
            }
            _ => false,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn gain(&mut self, cx: &mut Cx, exp: &Val, found: &Val, pol: Variance, via: Via, in_result: bool, depth: usize, w: &Walk) -> Option<Gained> {
        if depth > 16 {
            return None;
        }
        let (e, f) = (self.peel(exp), self.peel(found));
        let (ea, fa) = (self.refined_alias(&e), self.refined_alias(&f));
        if depth > 0 && (ea.is_some() || fa.is_some()) {
            let same = match (&ea, &fa) {
                (Some((d1, a1)), Some((d2, a2))) => {
                    d1 == d2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| unify(&self.g, cx.lvl(), x, y).is_ok())
                }
                _ => false,
            };
            if !same {
                let role = if pol == Variance::Contra && matches!(via, Via::Fn) {
                    WeakenRole::Param
                } else if in_result {
                    WeakenRole::Result
                } else {
                    WeakenRole::Element
                };
                // (sub, sup): every `sub` must be a `sup`.
                let pairs: Vec<(&Val, &Val)> = match pol {
                    Variance::Co => vec![(&f, &e)],
                    Variance::Contra => vec![(&e, &f)],
                    Variance::Inv => vec![(&f, &e), (&e, &f)],
                };
                for (sub, sup) in pairs {
                    // A `sub` whose alias `sup` refines further (`Nat` under
                    // `Small`) is its base, as an unrefined type is (D121).
                    let sub_ref = self.refined_alias(sub).is_some() && !self.refines(sup, sub);
                    let sup_ref = self.refined_alias(sup).is_some();
                    if !sup_ref {
                        continue;
                    }
                    if sub_ref || role == WeakenRole::Param {
                        self.weaken_obligation(cx, sub, sup, role, w);
                    } else {
                        // A class's type is shown as written (`Seq.Elem s`),
                        // not as its dictionary's field.
                        let f = if self.g.reads_type_field(&f) { found.clone() } else { f.clone() };
                        return Some(Gained { expected: e.clone(), found: f, variance: pol, via, cx: cx.clone() });
                    }
                }
            }
        }
        let (e, f) = (self.base(&e), self.base(&f));
        match (&e, &f) {
            (Val::TyCon(t1, a1), Val::TyCon(t2, a2)) if t1 == t2 && a1.len() == a2.len() => {
                let vs = self.variance(*t1);
                for (k, (x, y)) in a1.iter().zip(a2).enumerate() {
                    let v = vs.get(k).copied().unwrap_or(Variance::Inv);
                    let via = if v == Variance::Co { via } else { Via::Ty(*t1) };
                    if let Some(g) = self.gain(cx, x, y, pol.then(v), via, in_result, depth + 1, w) {
                        return Some(g);
                    }
                }
                None
            }
            (Val::TupleTy(x), Val::TupleTy(y)) if x.len() == y.len() => {
                for (a, b) in x.iter().zip(y) {
                    if let Some(g) = self.gain(cx, a, b, pol, via, in_result, depth + 1, w) {
                        return Some(g);
                    }
                }
                None
            }
            (Val::Pi(x1, _, _, a1, c1), Val::Pi(x2, _, _, a2, c2)) => {
                if let Some(g) = self.gain(cx, a1, a2, pol.then(Variance::Contra), Via::Fn, false, depth + 1, w) {
                    return Some(g);
                }
                // The result is compared for arguments the caller may pass:
                // those of the side that must be implied (D85).
                let (x, other, dom) = match pol {
                    Variance::Contra => (x2, x1, a2),
                    _ => (x1, x2, a1),
                };
                // An unnamed parameter (`Nat -> Nat`) takes the other side's
                // name, which its predicates use (`x <= n`); never a default
                // that another of its names may already have.
                let name = [x.as_ref(), other.as_ref()].into_iter().find(|n| *n != "_").map(str::to_string).unwrap_or_else(|| {
                    let taken = cx.names();
                    (0..).map(|k| if k == 0 { "x".to_string() } else { format!("x{k}") }).find(|n| !taken.iter().any(|t| t.as_ref() == n)).unwrap()
                });
                let name = name.as_str();
                let l = cx.lvl();
                cx.bind(name, (**dom).clone(), Mult::Zero);
                let (b1, b2) = (apply_closure(&self.g, c1, Val::var(l)), apply_closure(&self.g, c2, Val::var(l)));
                let r = self.gain(cx, &b1, &b2, pol, via, true, depth + 1, w);
                cx.pop();
                r
            }
            _ => None,
        }
    }

    /// A type as shown in a message: an inline refinement with its
    /// arguments put in (`(x~Nat, contains xs x)` for `(x~a, contains xs
    /// x)` at `a` = `Nat`), any other type as it is.
    fn show_refined(&self, cx: &Cx, v: &Val) -> String {
        match self.refined_alias(v) {
            Some((d, args)) if is_anon_alias(&self.g, d) && !args.is_empty() => {
                rename_words(&self.g.defs[d.0 as usize].name, &self.alias_param_names(cx, d, &args))
            }
            _ => self.show_val(cx, v),
        }
    }

    /// For any value of `sub`, the predicates of `sup` (D83, D85).
    fn weaken_obligation(&mut self, cx: &mut Cx, sub: &Val, sup: &Val, role: WeakenRole, w: &Walk) {
        let Some((alias, args)) = self.refined_alias(sup) else { return };
        let Some(preds) = self.alias_preds.get(&alias).cloned() else { return };
        let name = self.alias_subject.get(&alias).cloned().unwrap_or_else(|| Rc::from("x"));
        let (sub_s, sup_s) = (self.show_refined(cx, sub), self.show_refined(cx, sup));
        let l = cx.lvl();
        cx.bind(&name, sub.clone(), Mult::Zero);
        for p in &preds {
            let mut env = args.clone();
            env.push(Val::var(l));
            let goal = self.inst_pred(p, env);
            let kind = w.kind.clone().unwrap_or_else(|| ObKind::Weaken { role, value: w.value.clone(), sub: sub_s.clone(), sup: sup_s.clone(), callee: w.callee.clone() });
            let text = rename_words(&p.text, &self.alias_param_names(cx, alias, &args));
            self.oblige(cx, w.span, kind, text, goal, None);
        }
        cx.pop();
    }

    /// The obligations for a value `v` checked against refinement alias
    /// `alias` applied to `args` (D71).
    pub fn refined_obligation(&mut self, cx: &Cx, alias: DefId, args: Vec<Val>, v: Val, span: Span) {
        if Some(alias) == self.g.well_known.nat && self.nat_by_closure(cx, &v) {
            return; // D121 (c)
        }
        let Some(preds) = self.alias_preds.get(&alias).cloned() else { return };
        let name = self.g.defs[alias.0 as usize].name.to_string();
        let value = self.src_text(span);
        // The predicates in this use's names: `p <= 100`, not `n <= 100`.
        let mut names = self.alias_param_names(cx, alias, &args);
        if let Some(x) = self.alias_subject.get(&alias) {
            let shown = if value.contains(' ') { format!("({value})") } else { value.clone() };
            names.push((x.to_string(), shown));
        }
        for p in &preds {
            let mut env = args.clone();
            env.push(v.clone());
            let goal = self.inst_pred(p, env);
            let text = rename_words(&p.text, &names);
            self.oblige(cx, span, ObKind::Refined { alias: name.clone(), value: value.clone() }, text, goal, None);
        }
    }

    /// E0262: a refinement gained through a type argument.
    pub fn report_gained(&mut self, cx: &Cx, expected: &Val, found: &Val, g: &Gained, span: Span, what: &str) {
        let (e, f) = (self.show_val(cx, expected), self.show_val(cx, found));
        let (ge, gf) = (self.show_val(&g.cx, &g.expected), self.show_val(&g.cx, &g.found));
        let mut d = Diagnostic::error("E0262", format!("type mismatch: expected `{e}`, found `{f}`"), span);
        let ty = |t: TyId| self.g.tys[t.0 as usize].name.to_string();
        d = match (g.variance, g.via) {
            (Variance::Inv, Via::Ty(t)) if Some(t) == self.g.well_known.cown => d
                .with_label(format!("{what} has type `{f}`"))
                .with_note(format!("a cown's contents type must match exactly: `{gf}` and `{ge}` differ, and a behaviour on either side could write a value the other doesn't allow"))
                .with_help(format!("create the cown with the type `{e}`")),
            (Variance::Inv, Via::Ty(t)) if self.g.tys[t.0 as usize].is_abstract => d
                .with_label(format!("{what} has type `{f}`"))
                .with_note(format!("`{}`'s parameter has no polarity mark, so `{gf}` and `{ge}` must match exactly", ty(t)))
                .with_help(format!("if `{}` only holds values of its parameter, its module can mark it `+`", ty(t))),
            (Variance::Inv, _) => d
                .with_label(format!("{what} has type `{f}`"))
                .with_note(format!("`{gf}` and `{ge}` must match exactly here: the type is used both as input and as output"))
                .with_help(format!("give the value the type `{e}` where it is built")),
            (Variance::Contra, Via::Ty(t)) => d
                .with_label(format!("{what} has type `{f}`"))
                .with_note(format!("`{}` is marked `-`: a `{f}` accepts only `{gf}` values, but is used where any `{ge}` may be given to it", ty(t)))
                .with_help(format!("use a `{e}` here")),
            (Variance::Contra, _) => d
                .with_label(format!("{what} has type `{f}`"))
                .with_note(format!("this function needs a `{gf}`, but is given where any `{ge}` may be passed to it"))
                .with_help("check the argument inside the function instead, e.g. with an `if`"),
            (Variance::Co, _) => d
                .with_label(format!("{what} has type `{f}`, so its `{gf}` values aren't known to be `{ge}`"))
                .with_note("a refinement inside a type is never gained from an existing value: that would need a proof about every element")
                .with_help(format!("give the value the type `{e}` where it is built, so that each part is checked there")),
        };
        self.err(d);
    }

    /// An inline refinement `(n~Int, n >= 5)` or a refined function type
    /// `(x~A -> y~B, preds)` (D82): anonymous aliases, applied to the locals
    /// they mention.
    pub fn elab_refine(&mut self, cx: &mut Cx, r: &ast::RefineTy) -> Tm {
        let name = |i: &Option<ast::Ident>| i.as_ref().map_or("_".to_string(), |i| i.name.clone());
        let a = self.elab_type(cx, &r.dom);
        let a_text = self.src_text(r.dom.span);
        let av = self.eval(cx, &a);
        let x = name(&r.param);
        // A class function's own type variable (M25): an implicit, erased
        // parameter; or its own class clause, an implicit dictionary.
        if let (Some(p), Some((None, b_expr))) = (&r.param, &r.arrow) {
            if p.name.starts_with('\'') {
                let m = if self.class_clause(&r.dom).is_some() { Mult::Many } else { Mult::Zero };
                cx.bind(&p.name, av, m);
                let b = self.elab_type(cx, b_expr);
                cx.pop();
                return Tm::Pi(Rc::from(&p.name[1..]), m, Icit::Impl, Rc::new(a), Rc::new(b));
            }
        }
        let Some((res, b_expr)) = &r.arrow else {
            cx.bind(&x, av, Mult::Zero);
            let preds: Vec<Pred> = r.preds.iter().map(|e| self.elab_pred(cx, e, false)).collect();
            cx.pop();
            return self.anon_alias(cx, &x, &a_text, a, preds);
        };
        if r.own {
            self.check_own(cx, &a, r.dom.span);
        }
        let m = if r.own || self.type_linear(&a) { Mult::One } else { Mult::Many };
        cx.bind(&x, av, Mult::Zero);
        let b = self.elab_type(cx, b_expr);
        let b_text = self.src_text(b_expr.span);
        let bv = self.eval(cx, &b);
        let y = name(res);
        cx.bind(&y, bv, Mult::Zero);
        // An implicit argument in a predicate (`nonempty i` with `nonempty :
        // xs~List a`) is an unknown applied to every local in scope, the
        // result too. Its solution (`Int`) is substituted before asking which
        // locals a predicate mentions; one left open (`nonempty []`) can't
        // depend on the result: nothing about the result determined it.
        let preds: Vec<Pred> = r
            .preds
            .iter()
            .map(|e| {
                let p = self.elab_pred(cx, e, false);
                crate::core::forget_var(&self.g, cx.lvl(), &p.tm, cx.lvl() - 1);
                Pred { tm: crate::core::zonk_metas(&self.g, cx.lvl(), &p.tm), ..p }
            })
            .collect();
        cx.pop();
        // A predicate that mentions the result is a postcondition (D82).
        let (posts, pres): (Vec<Pred>, Vec<Pred>) = preds.into_iter().partition(|p| {
            let mut fv = std::collections::BTreeSet::new();
            free_vars(&p.tm, 0, &mut fv);
            res.is_some() && fv.contains(&0)
        });
        let cod = self.anon_alias(cx, &y, &b_text, b, posts);
        cx.pop();
        // The rest are over the parameter alone.
        let pres = pres
            .into_iter()
            .map(|p| Pred { tm: rename_free(&p.tm, 0, &|i| i - 1), ..p })
            .collect();
        let dom = self.anon_alias(cx, &x, &a_text, a, pres);
        Tm::Pi(Rc::from(x.as_str()), m, Icit::Expl, Rc::new(dom), Rc::new(cod))
    }

    /// The alias `subject~base, preds` (preds over the locals of `cx` and the
    /// subject), as a definition over just the locals it mentions, applied to
    /// them. No predicates: the base itself.
    fn anon_alias(&mut self, cx: &Cx, subject: &str, base_text: &str, base: Tm, preds: Vec<Pred>) -> Tm {
        if preds.is_empty() {
            return base;
        }
        let l = cx.lvl();
        let mut fv = std::collections::BTreeSet::new();
        free_vars(&base, 0, &mut fv);
        for p in &preds {
            free_vars(&p.tm, 1, &mut fv);
        }
        // Captured levels, outermost first.
        let mut levels: Vec<usize> = fv.iter().filter(|i| **i < l).map(|i| l - 1 - i).collect();
        levels.sort_unstable();
        let k = levels.len();
        let pos = |i: usize| -> usize {
            let lv = l - 1 - i;
            let p = levels.iter().position(|x| *x == lv).expect("a captured local");
            k - 1 - p
        };
        let text = format!(
            "({subject}~{base_text}, {})",
            preds.iter().map(|p| p.text.as_str()).collect::<Vec<_>>().join(", ")
        );
        let did = self.new_def(&text);
        let mut body = rename_free(&base, 0, &pos);
        let mut ty = Tm::Univ(0);
        for lv in levels.iter().rev() {
            let n = cx.locals[*lv].name.clone();
            body = Tm::Lam(n.clone(), Mult::Zero, Icit::Expl, Rc::new(body));
            ty = Tm::Pi(n, Mult::Zero, Icit::Expl, Rc::new(Tm::Univ(0)), Rc::new(ty));
        }
        let info = &mut self.g.defs[did.0 as usize];
        info.body = Some(body);
        info.ty = ty;
        let preds = preds.into_iter().map(|p| Pred { tm: rename_free(&p.tm, 1, &pos), ..p }).collect();
        self.alias_preds.insert(did, preds);
        self.alias_subject.insert(did, Rc::from(subject));
        let mut t = Tm::Def(did);
        for lv in &levels {
            t = Tm::App(Rc::new(t), Rc::new(Tm::Var(l - 1 - lv)), Icit::Expl, Mult::Zero);
        }
        t
    }

    /// The later binders a parameter's refined type (#102) needs the
    /// arguments of. Its refinements were elaborated before the class
    /// dictionaries they use were found, as unknowns over every local, so
    /// their aliases capture every parameter: once those are solved, only
    /// the parameters the aliases' predicates still mention count.
    pub fn late_deps(&self, late: &Late) -> Vec<usize> {
        let ty = crate::core::zonk_metas(&self.g, late.n, &late.ty);
        let mut free = std::collections::BTreeSet::new();
        self.used_free(&ty, 0, &mut free, 0);
        free.iter().filter(|i| **i < late.n).map(|i| late.n - 1 - i).filter(|j| *j > late.binder).collect()
    }

    /// `free_vars`, except that an argument of an inline refinement's alias
    /// counts only where the alias uses it.
    fn used_free(&self, t: &Tm, depth: usize, out: &mut std::collections::BTreeSet<usize>, nest: usize) {
        if let (Tm::Def(d), args) = t.spine() {
            if nest < 16 && !args.is_empty() && is_anon_alias(&self.g, *d) {
                let uses = self.alias_uses(*d, args.len(), nest + 1);
                for (a, used) in args.iter().zip(uses) {
                    if used {
                        self.used_free(a, depth, out, nest);
                    }
                }
                return;
            }
        }
        match t {
            Tm::Var(i) if *i >= depth => {
                out.insert(i - depth);
            }
            _ => t.each_sub(|x, n| self.used_free(x, depth + n, out, nest)),
        }
    }

    /// Which of its `k` captured locals an inline refinement's alias uses:
    /// in its base or, with what has been solved put in, its predicates.
    fn alias_uses(&self, d: DefId, k: usize, nest: usize) -> Vec<bool> {
        let mut free = std::collections::BTreeSet::new();
        match &self.g.defs[d.0 as usize].body {
            Some(body) => {
                let mut b = body;
                for _ in 0..k {
                    match b {
                        Tm::Lam(_, _, _, x) => b = x,
                        _ => return vec![true; k],
                    }
                }
                self.used_free(b, 0, &mut free, nest);
            }
            None => return vec![true; k],
        }
        for p in self.alias_preds.get(&d).into_iter().flatten() {
            let tm = crate::core::zonk_metas(&self.g, k + 1, &p.tm);
            self.used_free(&tm, 1, &mut free, nest);
        }
        (0..k).map(|p| free.contains(&(k - 1 - p))).collect()
    }

    /// The type of `t`, a function with a specification applied to fewer
    /// arguments than it has binders (none, for a bare name), as a refined
    /// function type (D85, D86): each remaining parameter carries the
    /// preconditions whose last binder it is, the result the
    /// postconditions, with the given arguments put in. Preconditions about
    /// given arguments alone are checked at the call (`call_obligations`).
    pub fn refined_fn_type(&mut self, cx: &Cx, t: &Tm, ty: Val) -> Val {
        let Tm::Def(d) = t.head() else { return ty };
        // A class's function at a known instance: the instance's function,
        // with its signature (#252).
        if self.class_methods.contains(d) {
            if !self.inst_reqs.is_empty() && self.class_use(cx, t).is_some_and(|u| !u.3) {
                self.solve_instances(false);
                self.retry_waiting(false);
            }
            if let Some((direct, dty)) = self.instance_value(cx, t) {
                return self.spec_fn_type(cx, &direct, dty);
            }
        }
        // An instance's function is used only in its dictionary, and called
        // only through the class's function, whose preconditions are its own
        // (D136): its field's type needs none of them.
        if self.inst_fns.contains(d) {
            return ty;
        }
        self.spec_fn_type(cx, t, ty)
    }

    /// A class's function applied to its dictionary and to fewer
    /// arguments than it takes, where the dictionary is a known
    /// instance's whose function has a signature of its own (#252): that
    /// function applied to the dictionary's arguments and the given ones,
    /// as a direct call of it would be (`known_instance`), and its type
    /// there. `None` when `t` isn't such a value.
    pub(super) fn instance_value(&self, cx: &Cx, t: &Tm) -> Option<(Tm, Val)> {
        let t = crate::core::zonk_metas(&self.g, cx.lvl(), t);
        let (h, args) = t.spine();
        let Tm::Def(f) = h else { return None };
        // The class's binders: `\ … {d} x y -> d.f x y`, at the given
        // arguments.
        let mut ty = eval(&self.g, &Rc::new(Vec::new()), &self.g.defs[f.0 as usize].ty);
        let mut binders = Vec::new();
        let mut body = self.g.defs[f.0 as usize].body.as_ref()?;
        let mut refined_param = false;
        let mut lcx = cx.clone();
        while let Tm::Lam(_, _, _, b) = body {
            let Val::Pi(x, m, i, dom, c) = self.force(&ty) else { return None };
            if i == Icit::Expl && self.has_refined(&lcx, &dom, 0) {
                refined_param = true;
            }
            let v = match args.get(binders.len()) {
                Some(a) => self.eval(cx, a),
                None => Val::var(lcx.bind(&x, (*dom).clone(), Mult::Zero)),
            };
            binders.push((i, m));
            ty = apply_closure(&self.g, &c, v);
            body = b;
        }
        let given = args.len();
        if given >= binders.len() {
            return None;
        }
        // The class's result type promises its refinement only where the
        // class's preconditions hold, which a call with the instance's
        // weaker ones needn't meet: where it has one, the value keeps the
        // class's signature.
        let class_pre = refined_param || self.specs.get(f).is_some_and(|s| s.preds.iter().any(|p| !p.is_post));
        if class_pre && self.has_refined(&lcx, &ty, 0) {
            return None;
        }
        // Called with a fresh local for each binder not given.
        let rest = binders.len() - given;
        let mut call = crate::core::rename_free(&t, 0, &|i| i + rest);
        for (j, (i, m)) in binders[given..].iter().enumerate() {
            call = Tm::App(Rc::new(call), Rc::new(Tm::Var(rest - 1 - j)), *i, *m);
        }
        let direct = crate::native::ir::known_instance(&self.g, &call)?;
        let mut spine = Vec::new();
        let mut h = &direct;
        while let Tm::App(g, a, i, m) = h {
            spine.push((a.clone(), *i, *m));
            h = g;
        }
        spine.reverse();
        let Tm::Def(g) = h else { return None };
        if !self.refined_inst_fns.contains(g) {
            return None;
        }
        // Those locals are its last arguments, in order; the others don't
        // mention them.
        let k = spine.len().checked_sub(rest)?;
        if (0..rest).any(|j| !matches!(*spine[k + j].0, Tm::Var(v) if v == rest - 1 - j)) {
            return None;
        }
        let mut out = Tm::Def(*g);
        let mut gty = eval(&self.g, &Rc::new(Vec::new()), &self.g.defs[g.0 as usize].ty);
        for (a, i, m) in &spine[..k] {
            let mut fv = std::collections::BTreeSet::new();
            free_vars(a, 0, &mut fv);
            if fv.first().is_some_and(|v| *v < rest) {
                return None;
            }
            let a = crate::core::rename_free(a, 0, &|v| v - rest);
            let Val::Pi(_, _, _, _, c) = self.force(&gty) else { return None };
            gty = apply_closure(&self.g, &c, self.eval(cx, &a));
            out = Tm::App(Rc::new(out), Rc::new(a), *i, *m);
        }
        Some((out, gty))
    }

    /// `refined_fn_type` for `t`, whose head is a function with a
    /// specification.
    pub(super) fn spec_fn_type(&mut self, cx: &Cx, t: &Tm, ty: Val) -> Val {
        let (h, args) = t.spine_cloned();
        let Tm::Def(d) = h else { return ty };
        let Some(spec) = self.specs.get(d).cloned() else { return ty };
        let n = spec.n_binders;
        let given = args.len();
        // A predicate of a binder's refinement alias (`x~Nat`) is carried by
        // the alias in the binder's type already.
        let spec_preds: Vec<Pred> = spec.preds.iter().filter(|p| p.alias.is_none()).cloned().collect();
        if given >= n || spec_preds.is_empty() {
            return ty;
        }
        // The last binder a predicate mentions (`n` for the result).
        let last = |p: &Pred| {
            let mut fv = std::collections::BTreeSet::new();
            free_vars(&p.tm, 0, &mut fv);
            fv.iter().map(|i| n - i).max()
        };
        let mut cx2 = cx.clone();
        let mut env: Vec<Val> = args.iter().map(|a| self.eval(cx, a)).collect();
        let mut cur = ty;
        // (name, mult, icit, domain) of each remaining binder, over `cx2`.
        let mut binders: Vec<(Name, Mult, Icit, Tm)> = Vec::new();
        for k in given..n {
            let Val::Pi(x, m, i, dom, c) = self.force(&cur) else { return cur };
            let l = cx2.lvl();
            let dom_tm = quote(&self.g, l, &dom);
            let mut preds = Vec::new();
            for p in spec_preds.iter().filter(|p| !p.is_post && last(p) == Some(k)) {
                let mut e = env.clone();
                e.push(Val::var(l));
                while e.len() <= n {
                    e.push(Val::Error);
                }
                preds.push(self.subst_pred(p, e, l + 1, &cx2, &x));
            }
            let text = self.show_val(&cx2, &dom);
            let alias = self.anon_alias(&cx2, &x, &text, dom_tm, preds);
            binders.push((x.clone(), m, i, alias));
            cx2.bind(&x, (*dom).clone(), Mult::Zero);
            env.push(Val::var(l));
            cur = apply_closure(&self.g, &c, Val::var(l));
        }
        let l = cx2.lvl();
        let cod = quote(&self.g, l, &cur);
        let res: Name = Rc::from(self.fn_meta.get(d).and_then(|m| m.result.clone()).unwrap_or_else(|| "result".to_string()).as_str());
        let mut posts = Vec::new();
        for p in spec_preds.iter().filter(|p| p.is_post && last(p) == Some(n)) {
            let mut e = env.clone();
            e.push(Val::var(l));
            posts.push(self.subst_pred(p, e, l + 1, &cx2, &res));
        }
        let text = self.show_val(&cx2, &cur);
        let mut out = self.anon_alias(&cx2, &res, &text, cod, posts);
        for (x, m, i, dom) in binders.into_iter().rev() {
            out = Tm::Pi(x, m, i, Rc::new(dom), Rc::new(out));
        }
        self.eval(cx, &out)
    }

    /// A predicate with its binders replaced by `env`, as a term over `l`
    /// locals (`cx2` and the subject `x`), shown with the arguments put in.
    fn subst_pred(&self, p: &Pred, env: Vec<Val>, l: usize, cx2: &Cx, x: &Name) -> Pred {
        let v = self.inst_pred(p, env);
        let tm = quote(&self.g, l, &v);
        let mut names = cx2.names();
        names.push(x.clone());
        let shown = show(&self.g, &names, &tm);
        let text = if shown.len() <= 2 * p.text.len() + 8 { shown } else { p.text.clone() };
        Pred { tm, text, ..p.clone() }
    }
}
