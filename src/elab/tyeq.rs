//! Type equations (#209, SPEC §9.3): `A == B` between two types.
//!
//! - **Wanted.** At each call or construction, a callee's equations at the
//!   use's types (`Wanted`), solved by unification once the types are
//!   known (`solve_wanted`); E0294 if one fails. Equal means identical,
//!   refinements included (`exact`).
//! - **Given.** In a body or a `match` arm, its equations hold (`givens`).
//!   Equal types form classes, each with a representative: a type with no
//!   stuck part (a type parameter, a class's type at a dictionary in scope)
//!   if there is one. Types are compared modulo them (`unify_at`), seen
//!   through them (`force`), and handed to the prover written with them
//!   (`obligation`), so the prover never sees an equation.

use super::*;
use crate::syntax::ast::{Constraint, Expr, ExprKind};
use crate::syntax::token::Op;

/// An equation as written in a signature or a constructor: its sides over
/// the binders then the result (a constructor's: its type's parameters,
/// then its fields).
#[derive(Clone, Debug)]
pub struct TyEq {
    pub lhs: Tm,
    pub rhs: Tm,
    pub text: String,
    pub span: Span,
}

/// An equation a use must meet, once its types are known.
pub struct Wanted {
    pub lvl: usize,
    pub names: Vec<Name>,
    pub lhs: Val,
    pub rhs: Val,
    pub span: Span,
    pub text: String,
    pub kind: WantedKind,
    pub owner: Option<DefId>,
    /// The equations that hold where the use is.
    pub givens: Vec<Given>,
}

pub enum WantedKind {
    /// `callee`'s equation; the parameters it names, at this call.
    Call { callee: String, params: Vec<(String, Val)> },
    /// Constructor `con` of type `tid`, at the type's arguments `args`; the
    /// parameter the equation fixes, if one side is one; the function it is
    /// an argument of, if any.
    Build { con: String, tid: TyId, args: Vec<Val>, fixes: Option<(usize, bool)>, taken_by: Option<String> },
}

/// An equation that holds in the scope being checked.
#[derive(Clone)]
pub struct Given {
    pub a: Val,
    pub b: Val,
    pub text: String,
}

/// The classes of equal types the givens make: each class's members, its
/// representative's index, and the equation that put each member there.
struct Classes {
    members: Vec<Vec<(Val, String)>>,
    rep: Vec<usize>,
}

impl Elab {
    /// The sides of `e` if it is a type equation: `A == B` where a side is
    /// a type by its head (a type's name, a class's type `C.Name`) or a
    /// name the constraints `cs` give the type `Type`.
    pub fn teq_sides<'a>(&self, cs: &[Constraint], e: &'a Expr) -> Option<(&'a Expr, &'a Expr)> {
        self.teq_sides_in(cs, &[], e)
    }

    /// As `teq_sides`, where `types` are names of types in scope too (a
    /// type's parameters of kind `Type`).
    pub fn teq_sides_in<'a>(&self, cs: &[Constraint], types: &[String], e: &'a Expr) -> Option<(&'a Expr, &'a Expr)> {
        let ExprKind::Binary(Op::EqEq, a, b) = &e.kind else { return None };
        let named = |x: &Expr| matches!(&x.kind, ExprKind::Var(n) if types.contains(n));
        (self.type_like(cs, a) || self.type_like(cs, b) || named(a) || named(b)).then_some((&**a, &**b))
    }

    /// A type's parameters of kind `Type`, by name.
    pub fn type_params_named(&self, tid: TyId) -> Vec<String> {
        self.g.tys[tid.0 as usize].params.iter().filter(|(_, k)| matches!(k, Tm::Univ(_))).map(|(n, _)| n.to_string()).collect()
    }

    fn type_like(&self, cs: &[Constraint], e: &Expr) -> bool {
        let mut h = e;
        while let ExprKind::App(f, _) = &h.kind {
            h = f;
        }
        match &h.kind {
            ExprKind::Con(n) => match self.resolve(n, false) {
                Some(Sym::Ty(_)) => true,
                Some(Sym::Def(d)) => is_type_former(&self.g.defs[d.0 as usize].ty),
                _ => false,
            },
            // `C.Name`: a class's type.
            ExprKind::Field(q, name) => matches!(&q.kind, ExprKind::Con(n)
                if matches!(self.resolve(n, true), Some(Sym::Ty(t)) if self.class_defs.get(&t).is_some_and(|c| c.types().contains(&name.name)))),
            ExprKind::Var(n) => cs.iter().any(|c| match c {
                Constraint::Typed { name, ty, .. } => name.name == *n && matches!(&ty.kind, ExprKind::Con(t) if t == "Type"),
                _ => false,
            }),
            ExprKind::Tuple(_) | ExprKind::Arrow(..) => true,
            _ => false,
        }
    }

    /// Elaborate a type equation's sides in `cx`, as types: `None` (with
    /// E0295) if one side is a type parameter the other contains.
    pub fn elab_teq(&mut self, cx: &mut Cx, e: &Expr, a: &Expr, b: &Expr) -> Option<(Tm, Tm)> {
        let l = self.elab_type(cx, a);
        let r = self.elab_type(cx, b);
        let (lv, rv) = (self.eval(cx, &l), self.eval(cx, &r));
        for (x, y, xs) in [(&lv, &rv, a), (&rv, &lv, b)] {
            if let Val::Neutral(Head::Var(v), sp) = force_meta(&self.g, x.clone()) {
                let inside = crate::core::zonk_metas(&self.g, cx.lvl(), &quote(&self.g, cx.lvl(), y));
                if sp.is_empty() && !matches!(force_meta(&self.g, y.clone()), Val::Neutral(Head::Var(w), _) if w == v) && mentions_level(&inside, cx.lvl(), v) {
                    let text = self.src_text(e.span);
                    let name = self.src_text(xs.span);
                    self.err(
                        Diagnostic::error("E0295", format!("`{text}` can't hold: `{name}` would contain itself"), e.span)
                            .with_label("no type is equal to a type it is part of"),
                    );
                    return None;
                }
            }
        }
        Some((l, r))
    }

    /// E0296: a type equation where it can only be promised.
    pub fn teq_promised(&mut self, e: &Expr, what: &str) {
        let d = Diagnostic::error("E0296", what.to_string(), e.span);
        let d = if what.contains("assumed") { d.with_help("state it as a constraint on a parameter") } else { d };
        self.err(d);
    }

    // ── given ───────────────────────────────────────────────────────────

    fn same_plain(&self, a: &Val, b: &Val) -> bool {
        self.same_type(&force(&self.g, a.clone()), &force(&self.g, b.clone()))
    }

    /// Does `v` have no stuck part: no type parameter, no class's type at a
    /// dictionary in scope, nothing unknown?
    fn ground(&self, v: &Val) -> bool {
        let t = quote(&self.g, 1 << 20, v);
        crate::core::max_var(&t).is_none() && !has_meta(&t)
    }

    fn eq_classes(&self) -> Classes {
        let mut members: Vec<Vec<(Val, String)>> = Vec::new();
        let find = |members: &Vec<Vec<(Val, String)>>, v: &Val| members.iter().position(|c| c.iter().any(|(m, _)| self.same_plain(m, v)));
        for g in &self.givens {
            let (ia, ib) = (find(&members, &g.a), find(&members, &g.b));
            match (ia, ib) {
                (Some(i), Some(j)) if i != j => {
                    let (lo, hi) = (i.min(j), i.max(j));
                    let moved = members.remove(hi);
                    members[lo].extend(moved);
                }
                (Some(_), Some(_)) => {}
                (Some(i), None) => members[i].push((g.b.clone(), g.text.clone())),
                (None, Some(j)) => members[j].push((g.a.clone(), g.text.clone())),
                (None, None) => members.push(vec![(g.a.clone(), g.text.clone()), (g.b.clone(), g.text.clone())]),
            }
        }
        let rep = members.iter().map(|c| c.iter().position(|(m, _)| self.ground(m)).unwrap_or(0)).collect();
        Classes { members, rep }
    }

    /// The representative of `v`'s class, if `v` is a member that isn't it.
    pub fn rep_of(&self, v: &Val) -> Option<Val> {
        if self.givens.is_empty() {
            return None;
        }
        let cs = self.eq_classes();
        for (c, &r) in cs.members.iter().zip(&cs.rep) {
            if c.iter().enumerate().any(|(k, (m, _))| k != r && self.same_plain(m, v)) && !self.same_plain(&c[r].0, v) {
                return Some(c[r].0.clone());
            }
        }
        None
    }

    /// Each type in the equations in scope that has a representative, and it.
    pub fn rep_pairs(&self) -> Vec<(Val, Val)> {
        if self.givens.is_empty() {
            return Vec::new();
        }
        let cs = self.eq_classes();
        let mut out = Vec::new();
        for (c, &r) in cs.members.iter().zip(&cs.rep) {
            for (k, (m, _)) in c.iter().enumerate() {
                if k != r {
                    out.push((m.clone(), c[r].0.clone()));
                }
            }
        }
        out
    }

    /// The same type, after unfolding at their heads (no unknown solved).
    pub fn same_type_forced(&self, a: &Val, b: &Val) -> bool {
        self.same_plain(a, b)
    }

    /// Two equations in scope that can't both hold: their texts.
    pub fn contradiction(&self) -> Option<(String, String)> {
        let cs = self.eq_classes();
        for c in &cs.members {
            let grounds: Vec<&(Val, String)> = c.iter().filter(|(m, _)| self.ground(m)).collect();
            for (k, (x, tx)) in grounds.iter().enumerate() {
                for (y, ty) in &grounds[k + 1..] {
                    if !self.exact(0, x, y) {
                        let (a, b) = if tx == ty { (tx.clone(), tx.clone()) } else { (tx.clone(), ty.clone()) };
                        return Some((a, b));
                    }
                }
            }
        }
        None
    }

    /// `v`, over `lvl` locals, with each type in it that has a
    /// representative written as it.
    pub fn rep_deep(&self, lvl: usize, v: &Val) -> Val {
        if self.givens.is_empty() {
            return v.clone();
        }
        let t = quote(&self.g, lvl, v);
        let t = self.rep_tm(lvl, &t);
        let env = Rc::new((0..lvl).map(Val::var).collect::<Vec<_>>());
        eval(&self.g, &env, &t)
    }

    fn rep_tm(&self, lvl: usize, t: &Tm) -> Tm {
        if !matches!(t, Tm::Lit(_) | Tm::Univ(_) | Tm::Error) {
            let env = Rc::new((0..lvl).map(Val::var).collect::<Vec<_>>());
            if let Some(r) = self.rep_of(&eval(&self.g, &env, t)) {
                return quote(&self.g, lvl, &r);
            }
        }
        t.map_sub(|x, k| self.rep_tm(lvl + k, x))
    }

    /// Assume equations `eqs` (each the two sides and its text) for the
    /// scope; how many givens there were, to restore.
    pub fn assume_teqs(&mut self, eqs: Vec<(Val, Val, String)>) -> usize {
        let n = self.givens.len();
        for (a, b, text) in eqs {
            self.givens.push(Given { a, b, text });
        }
        n
    }

    // ── wanted ──────────────────────────────────────────────────────────

    /// Equal, refinements included: two types that unify, compared without
    /// unfolding a refinement alias.
    pub fn exact(&self, lvl: usize, a: &Val, b: &Val) -> bool {
        if unify(&self.g, lvl, a, b).is_err() {
            return false;
        }
        self.exact_inner(lvl, a, b, 0)
    }

    fn exact_inner(&self, lvl: usize, a: &Val, b: &Val, depth: usize) -> bool {
        if depth > 32 {
            return true;
        }
        let (pa, pb) = (self.peel(a), self.peel(b));
        match (self.refined_alias(&pa), self.refined_alias(&pb)) {
            (Some((d1, x1)), Some((d2, x2))) => {
                return d1 == d2 && x1.len() == x2.len() && x1.iter().zip(&x2).all(|(x, y)| self.exact_inner(lvl, x, y, depth + 1));
            }
            (Some(_), None) | (None, Some(_)) => return false,
            _ => {}
        }
        match (force(&self.g, pa), force(&self.g, pb)) {
            (Val::TyCon(t1, x1), Val::TyCon(t2, x2)) => t1 == t2 && x1.iter().zip(x2.iter()).all(|(x, y)| self.exact_inner(lvl, x, y, depth + 1)),
            (Val::TupleTy(x1), Val::TupleTy(x2)) => x1.len() == x2.len() && x1.iter().zip(x2.iter()).all(|(x, y)| self.exact_inner(lvl, x, y, depth + 1)),
            (Val::Pi(_, _, _, a1, c1), Val::Pi(_, _, _, a2, c2)) => {
                self.exact_inner(lvl, &a1, &a2, depth + 1)
                    && self.exact_inner(lvl + 1, &apply_closure(&self.g, &c1, Val::var(lvl)), &apply_closure(&self.g, &c2, Val::var(lvl)), depth + 1)
            }
            _ => true,
        }
    }

    /// The equations of `d` (a function) or `c` (a constructor) at a use:
    /// wanted, solved once the use's types are known.
    pub fn want_call_teqs(&mut self, cx: &Cx, d: DefId, call: &Tm, args: &[Rc<Tm>], span: Span) {
        let Some(spec) = self.specs.get(&d) else { return };
        if spec.teqs.is_empty() || args.len() < spec.n_binders {
            return;
        }
        let (teqs, n) = (spec.teqs.clone(), spec.n_binders);
        let names = spec.binder_names.clone();
        let mut env: Vec<Val> = args[..n].iter().map(|a| self.eval(cx, a)).collect();
        env.push(self.eval(cx, call)); // the result slot; equations don't mention it
        let callee = self.g.defs[d.0 as usize].name.to_string();
        for q in teqs {
            let params = names
                .iter()
                .enumerate()
                .filter(|(_, n)| super::rename_words(&q.text, &[(n.to_string(), "\u{0}".into())]).contains('\u{0}'))
                .map(|(k, n)| (n.to_string(), env[k].clone()))
                .collect();
            let (lhs, rhs) = (self.inst_tm(&q.lhs, &env), self.inst_tm(&q.rhs, &env));
            self.wanted.push(Wanted {
                lvl: cx.lvl(),
                names: cx.names(),
                lhs,
                rhs,
                span,
                text: q.text.clone(),
                kind: WantedKind::Call { callee: callee.clone(), params },
                owner: self.cur_fn,
                givens: self.givens.clone(),
            });
        }
    }

    pub fn want_con_teqs(&mut self, cx: &Cx, c: ConId, args: &[Rc<Tm>], span: Span) {
        let tid0 = self.g.cons[c.0 as usize].ty;
        if !self.con_teqs.contains_key(&c) && !self.ty_teqs.contains_key(&tid0) {
            return;
        }
        let teqs = self.con_teqs.get(&c).cloned().unwrap_or_default();
        if args.len() < self.g.arity_con(c) {
            return;
        }
        let tid = self.g.cons[c.0 as usize].ty;
        let np = self.g.tys[tid.0 as usize].params.len();
        let env: Vec<Val> = args.iter().map(|a| self.eval(cx, a)).collect();
        let con = self.g.cons[c.0 as usize].name.to_string();
        let taken_by = self.arg_of.clone();
        // The type's own equations on its parameters, at the value built.
        for q in self.ty_teqs.get(&tid).cloned().unwrap_or_default() {
            self.want_type_teq(cx, tid, &env[..np], &q, span);
        }
        for q in teqs {
            let param = |t: &Tm| match t {
                Tm::Var(i) if *i >= env.len() - np => Some(env.len() - 1 - i),
                _ => None,
            };
            let fixes = param(&q.lhs).map(|k| (k, true)).or(param(&q.rhs).map(|k| (k, false)));
            let (lhs, rhs) = (self.inst_tm(&q.lhs, &env), self.inst_tm(&q.rhs, &env));
            self.wanted.push(Wanted {
                lvl: cx.lvl(),
                names: cx.names(),
                lhs,
                rhs,
                span,
                text: q.text.clone(),
                kind: WantedKind::Build { con: con.clone(), tid, args: env[..np].to_vec(), fixes, taken_by: taken_by.clone() },
                owner: self.cur_fn,
                givens: self.givens.clone(),
            });
        }
    }

    /// The type constructor `c` builds where its equations `teqs`, at its
    /// type's parameters and fields `all`, fix a parameter.
    pub fn built_type(&self, cx: &Cx, c: ConId, teqs: &[TyEq], all: &[Val]) -> String {
        let tid = self.g.cons[c.0 as usize].ty;
        let np = self.g.tys[tid.0 as usize].params.len();
        let mut args: Vec<Val> = all[..np].to_vec();
        for q in teqs {
            for (side, other) in [(&q.lhs, &q.rhs), (&q.rhs, &q.lhs)] {
                if let Tm::Var(i) = side {
                    if *i >= all.len() - np {
                        args[all.len() - 1 - i] = self.inst_tm(other, all);
                    }
                }
            }
        }
        self.show_val(cx, &Val::TyCon(tid, args.into()))
    }

    /// The equation `l == r` of type `tid`'s header (as written, `text`),
    /// at a place it is written with arguments: wanted.
    pub fn want_type_teq(&mut self, cx: &Cx, tid: TyId, args: &[Val], q: &TyEq, span: Span) {
        let ty = self.g.tys[tid.0 as usize].name.to_string();
        let env = Rc::new(args.to_vec());
        let (lhs, rhs) = (eval(&self.g, &env, &q.lhs), eval(&self.g, &env, &q.rhs));
        // The type's parameters the equation names, at this use.
        let params = self.g.tys[tid.0 as usize]
            .params
            .iter()
            .zip(args)
            .filter(|((n, _), _)| super::rename_words(&q.text, &[(n.to_string(), "\u{0}".into())]).contains('\u{0}'))
            .map(|((n, _), a)| (n.to_string(), a.clone()))
            .collect();
        self.wanted.push(Wanted {
            lvl: cx.lvl(),
            names: cx.names(),
            lhs,
            rhs,
            span,
            text: q.text.clone(),
            kind: WantedKind::Call { callee: ty, params },
            owner: self.cur_fn,
            givens: self.givens.clone(),
        });
    }

    /// The equations of the types applied in `v` (over `lvl` locals), at
    /// any depth outside a binder: each at its arguments, with its text and
    /// its type.
    pub fn ty_teqs_in(&self, lvl: usize, v: &Val) -> Vec<(TyId, Vec<Val>, TyEq)> {
        let mut out = Vec::new();
        if self.ty_teqs.is_empty() {
            return out;
        }
        let t = crate::core::zonk_metas(&self.g, lvl, &quote(&self.g, lvl, v));
        self.ty_teqs_tm(lvl, &t, &mut out);
        out
    }

    fn ty_teqs_tm(&self, lvl: usize, t: &Tm, out: &mut Vec<(TyId, Vec<Val>, TyEq)>) {
        let env = Rc::new((0..lvl).map(Val::var).collect::<Vec<_>>());
        let (head, args): (Option<TyId>, Vec<Tm>) = match t {
            Tm::TyConApp(tid, xs) => (Some(*tid), xs.clone()),
            _ => match t.spine() {
                (Tm::TyCon(tid), xs) => (Some(*tid), xs.into_iter().map(|x| (**x).clone()).collect()),
                _ => (None, Vec::new()),
            },
        };
        if let (Some(tid), Some(teqs)) = (head, head.and_then(|h| self.ty_teqs.get(&h))) {
            if args.len() >= self.g.tys[tid.0 as usize].params.len() {
                let avals: Vec<Val> = args.iter().map(|a| eval(&self.g, &env, a)).collect();
                for q in teqs {
                    out.push((tid, avals.clone(), q.clone()));
                }
            }
        }
        // Outside binders only: the arguments' types.
        if !matches!(t, Tm::Pi(..) | Tm::Lam(..)) {
            t.any_sub(|x, k| {
                if k == 0 {
                    self.ty_teqs_tm(lvl, x, out);
                }
                false
            });
        }
    }

    fn inst_tm(&self, t: &Tm, env: &[Val]) -> Val {
        eval(&self.g, &Rc::new(env.to_vec()), t)
    }

    /// Solve the wanted equations whose types are known; at the `last`
    /// try, report those that fail (E0294). One whose types never become
    /// known is dropped: its unknown is reported (E0285).
    pub fn solve_wanted(&mut self, last: bool) {
        let ws = std::mem::take(&mut self.wanted);
        let saved = std::mem::take(&mut self.givens);
        for w in ws {
            self.givens = w.givens.clone();
            // A class's type at a dictionary not found yet: once it is.
            if self.class_type_pending(&w.lhs) || self.class_type_pending(&w.rhs) {
                if !last {
                    self.wanted.push(w);
                }
                continue;
            }
            // A class's type at a known instance, as the instance gives it.
            let env = Rc::new((0..w.lvl).map(Val::var).collect::<Vec<_>>());
            let (l, rr) = (
                eval(&self.g, &env, &self.reduce_assoc(w.lvl, &quote(&self.g, w.lvl, &w.lhs))),
                eval(&self.g, &env, &self.reduce_assoc(w.lvl, &quote(&self.g, w.lvl, &w.rhs))),
            );
            let mut r = unify(&self.g, w.lvl, &l, &rr);
            // Modulo the equations where the use is.
            if !self.givens.is_empty() && (r.is_err() || !self.exact(w.lvl, &w.lhs, &w.rhs)) {
                let (a, b) = (self.rep_deep(w.lvl, &w.lhs), self.rep_deep(w.lvl, &w.rhs));
                if unify(&self.g, w.lvl, &a, &b).is_ok() && self.exact(w.lvl, &a, &b) {
                    continue;
                }
                r = unify(&self.g, w.lvl, &a, &b);
            }
            let waiting = {
                let mut p = self.g.postponed.borrow_mut();
                let again = !p.is_empty();
                p.clear();
                again
            };
            if waiting {
                if !last {
                    self.wanted.push(w);
                }
                continue;
            }
            if r.is_ok() && self.exact(w.lvl, &w.lhs, &w.rhs) {
                continue;
            }
            if r.is_err() && !last && self.has_unknown(w.lvl, &w.lhs, &w.rhs) {
                self.wanted.push(w);
                continue;
            }
            self.report_wanted(&w, r.is_ok());
        }
        self.givens = saved;
    }

    fn has_unknown(&self, lvl: usize, a: &Val, b: &Val) -> bool {
        [a, b].iter().any(|v| has_meta(&crate::core::zonk_metas(&self.g, lvl, &quote(&self.g, lvl, &force(&self.g, (*v).clone())))))
    }

    fn show_at(&self, w: &Wanted, v: &Val) -> String {
        let t = crate::core::zonk_metas(&self.g, w.lvl, &quote(&self.g, w.lvl, v));
        crate::core::show_marked(&self.g, &w.names, &t)
    }

    fn report_wanted(&mut self, w: &Wanted, only_refinements: bool) {
        let saved = self.cur_fn;
        self.cur_fn = w.owner;
        let mut d = match &w.kind {
            WantedKind::Call { callee, params } => {
                let mut parts = Vec::new();
                for (n, v) in params {
                    let mut part = format!("`{n}` is `{}`", self.show_at(w, v));
                    // A class's type at it, as the use computes it.
                    for side in [&w.lhs, &w.rhs] {
                        if let Some(name) = self.class_type_name(side) {
                            let at = crate::core::class_type_at(&self.g, side).unwrap_or_else(|| side.clone());
                            part.push_str(&format!(", whose `{name}` is `{}`", self.show_at(w, &at)));
                        }
                    }
                    parts.push(part);
                }
                let here = if parts.is_empty() {
                    format!("`{}` and `{}` differ", self.show_at(w, &w.lhs), self.show_at(w, &w.rhs))
                } else {
                    parts.join(" and ")
                };
                Diagnostic::error("E0294", format!("`{callee}` needs `{}`, but here {here}", w.text), w.span)
            }
            WantedKind::Build { con, tid, args, fixes, taken_by } => {
                let expected = self.show_at(w, &Val::TyCon(*tid, args.clone().into()));
                let mut built = args.clone();
                if let Some((k, lhs_is_param)) = fixes {
                    built[*k] = if *lhs_is_param { w.rhs.clone() } else { w.lhs.clone() };
                }
                let built = self.show_at(w, &Val::TyCon(*tid, built.into()));
                let wants = match taken_by {
                    Some(f) => format!("`{f}` takes {} `{expected}`", article(&expected)),
                    None => format!("{} `{expected}` is expected here", article(&expected)),
                };
                Diagnostic::error("E0294", format!("`{con}` builds {} `{built}`, but {wants}", article(&built)), w.span)
            }
        };
        if only_refinements {
            // The same type but for a refinement one side has: name it.
            let at = |v: &Val| crate::core::class_type_at(&self.g, v).unwrap_or_else(|| v.clone());
            let (l, r) = (at(&w.lhs), at(&w.rhs));
            let refined = |v: &Val| self.refined_alias(&self.peel(v));
            let pair = match (refined(&l), refined(&r)) {
                (Some(a), None) => Some((a, &l, &r)),
                (None, Some(a)) => Some((a, &r, &l)),
                _ => None,
            };
            if let Some(((alias, _), narrow, wide)) = pair {
                let (narrow, wide) = (self.show_at(w, narrow), self.show_at(w, wide));
                let preds: Vec<String> = self.alias_preds.get(&alias).map(|ps| ps.iter().map(|p| p.text.clone()).collect()).unwrap_or_default();
                d = d.with_help(format!(
                    "`{narrow}` and `{wide}` are different types: {} `{wide}` needn't satisfy `{}`",
                    article(&wide),
                    preds.join(" and ")
                ));
            }
        }
        self.err(d);
        self.cur_fn = saved;
    }

    /// `C.Name` if `v` is a class's type `C.Name t`, as written.
    fn class_type_name(&self, v: &Val) -> Option<String> {
        match force_meta(&self.g, v.clone()) {
            Val::Neutral(Head::Def(d), sp) if self.g.assoc_def(d).is_some_and(|(_, _, n)| sp.len() == n + 1) => Some(self.g.defs[d.0 as usize].name.to_string()),
            _ => None,
        }
    }
}

/// `a` or `an`, for a word shown after it.
pub fn article(word: &str) -> &'static str {
    match word.trim_start_matches('(').chars().next() {
        Some(c) if "AEIOUaeiou".contains(c) => "an",
        _ => "a",
    }
}

/// Does `t`, over `lvl` locals, mention local `level`?
/// An unknown's arguments (the locals it may depend on) don't count.
fn mentions_level(t: &Tm, lvl: usize, level: usize) -> bool {
    let mut found = false;
    fn go(t: &Tm, depth: usize, target: usize, found: &mut bool) {
        if let Tm::Var(i) = t {
            if *i >= depth && *i - depth == target {
                *found = true;
            }
        }
        if matches!(t.head(), Tm::Meta(_)) {
            return;
        }
        t.any_sub(|x, k| {
            go(x, depth + k, target, found);
            false
        });
    }
    go(t, 0, lvl - 1 - level, &mut found);
    found
}

/// Does `t` mention an unknown?
fn has_meta(t: &Tm) -> bool {
    matches!(t, Tm::Meta(_)) || t.any_sub(|x, _| has_meta(x))
}
