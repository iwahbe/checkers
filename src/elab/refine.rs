//! Refinements inside type arguments (D71, §7.1).
//!
//! A refinement alias (`type Small = n~Nat, n < 10`) is the same type as its
//! base for unification, so on its own `List Nat` would pass for
//! `List Small`. Two rules keep the alias meaningful:
//!
//! - A value checked against a refinement alias gets the alias's predicates
//!   as obligations (`refined_obligation`), unless the call or constructor
//!   it is an argument of already checks them (a parameter or field whose
//!   declared type is the alias).
//! - After unification, the expected and found types are compared by
//!   variance (`refined_mismatch`): a refinement inside a type argument may
//!   be forgotten (`List Small` as `List Nat`) but never gained (E0262).

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
    fn peel(&self, v: &Val) -> Val {
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

    /// Compare an expected and a found type that unify: the first place
    /// where the found type would gain a refinement it doesn't have.
    pub fn refined_mismatch(&self, cx: &Cx, expected: &Val, found: &Val) -> Option<Gained> {
        self.gain(cx, expected, found, Variance::Co, Via::Nothing, 0, 0)
    }

    #[allow(clippy::too_many_arguments)]
    fn gain(&self, cx: &Cx, exp: &Val, found: &Val, pol: Variance, via: Via, depth: usize, binders: usize) -> Option<Gained> {
        if depth > 16 {
            return None;
        }
        let (e, f) = (self.peel(exp), self.peel(found));
        let (ea, fa) = (self.refined_alias(&e), self.refined_alias(&f));
        if depth > 0 && (ea.is_some() || fa.is_some()) {
            let same = match (&ea, &fa) {
                (Some((d1, a1)), Some((d2, a2))) => {
                    d1 == d2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| unify(&self.g, cx.lvl() + binders, x, y).is_ok())
                }
                _ => false,
            };
            if same {
                return None;
            }
            // Which side must have the refinement the other lacks?
            let bad = match pol {
                Variance::Co => ea.is_some(),
                Variance::Contra => fa.is_some(),
                Variance::Inv => true,
            };
            if bad {
                return Some(Gained { expected: e, found: f, variance: pol, via });
            }
        }
        let (e, f) = (self.base(&e), self.base(&f));
        match (&e, &f) {
            (Val::TyCon(t1, a1), Val::TyCon(t2, a2)) if t1 == t2 && a1.len() == a2.len() => {
                let vs = self.variance(*t1);
                a1.iter().zip(a2).enumerate().find_map(|(k, (x, y))| {
                    let v = vs.get(k).copied().unwrap_or(Variance::Inv);
                    let via = if v == Variance::Co { via } else { Via::Ty(*t1) };
                    self.gain(cx, x, y, pol.then(v), via, depth + 1, binders)
                })
            }
            (Val::TupleTy(x), Val::TupleTy(y)) if x.len() == y.len() => {
                x.iter().zip(y).find_map(|(a, b)| self.gain(cx, a, b, pol, via, depth + 1, binders))
            }
            (Val::Pi(_, _, _, a1, c1), Val::Pi(_, _, _, a2, c2)) => {
                if let Some(g) = self.gain(cx, a1, a2, pol.then(Variance::Contra), Via::Fn, depth + 1, binders) {
                    return Some(g);
                }
                let x = Val::var(cx.lvl() + binders);
                let (b1, b2) = (apply_closure(&self.g, c1, x.clone()), apply_closure(&self.g, c2, x));
                self.gain(cx, &b1, &b2, pol, via, depth + 1, binders + 1)
            }
            _ => None,
        }
    }

    /// The obligations for a value `v` checked against refinement alias
    /// `alias` applied to `args` (D71).
    pub fn refined_obligation(&mut self, cx: &Cx, alias: DefId, args: Vec<Val>, v: Val, span: Span) {
        let Some(preds) = self.alias_preds.get(&alias).cloned() else { return };
        let name = self.g.defs[alias.0 as usize].name.to_string();
        let value = self.src_text(span);
        for p in &preds {
            let mut env = args.clone();
            env.push(v.clone());
            let goal = self.inst_pred(p, env);
            self.oblige(cx, span, ObKind::Refined { alias: name.clone(), value: value.clone() }, p.text.clone(), goal, None);
        }
    }

    /// E0262: a refinement gained through a type argument.
    pub fn report_gained(&mut self, cx: &Cx, expected: &Val, found: &Val, g: &Gained, span: Span, what: &str) {
        let (e, f) = (self.show_val(cx, expected), self.show_val(cx, found));
        let (ge, gf) = (self.show_val(cx, &g.expected), self.show_val(cx, &g.found));
        let mut d = Diagnostic::error("E0262", format!("type mismatch: expected `{e}`, found `{f}`"), span);
        let ty = |t: TyId| self.g.tys[t.0 as usize].name.to_string();
        d = match (g.variance, g.via) {
            (Variance::Inv, Via::Ty(t)) if Some(t) == self.g.well_known.cown => d
                .with_label(format!("{what} has type `{f}`"))
                .with_note(format!("a cown's contents type must match exactly: `{gf}` and `{ge}` differ, and a behaviour on either side could write a value the other doesn't allow"))
                .with_help(format!("create the cown with the type `{e}`")),
            (Variance::Inv, Via::Ty(t)) if self.g.tys[t.0 as usize].is_abstract => d
                .with_label(format!("{what} has type `{f}`"))
                .with_note(format!("`{}`'s parameter has no polarity mark, so `{gf}` and `{ge}` must match exactly (D16)", ty(t)))
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
                .with_note("a refinement inside a type is never gained from an existing value: that would need a proof about every element (D71)")
                .with_help(format!("give the value the type `{e}` where it is built, so that each part is checked there")),
        };
        self.err(d);
    }
}
