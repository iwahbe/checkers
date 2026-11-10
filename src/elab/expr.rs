//! Expressions: bidirectional checking and inference.

use super::*;
use crate::syntax::ast::{Expr, ExprKind, Ident, Stmt};
use crate::syntax::token::Op;

/// The body of a match arm: an expression, or the rest of a block (for `let` patterns).
#[derive(Clone, Copy)]
pub enum ArmBody<'a> {
    Expr(&'a Expr),
    Rest(&'a [Stmt], &'a Expr),
}

fn mk(kind: ExprKind, span: Span) -> Expr {
    Expr { kind, span }
}

impl Elab {
    // ── entry points ────────────────────────────────────────────────────────

    pub fn check_block(&mut self, cx: &mut Cx, b: &ast::Block, expected: &Val, tail: bool) -> Tm {
        self.block_from(cx, &b.stmts, &b.result, expected, tail)
    }

    pub fn arm_body(&mut self, cx: &mut Cx, body: ArmBody, expected: &Val, tail: bool) -> Tm {
        match body {
            ArmBody::Expr(e) => self.check(cx, e, expected, tail),
            ArmBody::Rest(stmts, result) => self.block_from(cx, stmts, result, expected, tail),
        }
    }

    /// Insert implicit applications until the type is not an implicit Π.
    pub fn insert(&mut self, cx: &Cx, mut t: Tm, mut ty: Val) -> (Tm, Val) {
        loop {
            match self.force(&ty) {
                Val::Pi(_, m, Icit::Impl, _, c) => {
                    let mt = self.fresh_meta(cx);
                    let mv = self.eval(cx, &mt);
                    t = Tm::App(Rc::new(t), Rc::new(mt), Icit::Impl, m);
                    ty = apply_closure(&self.g, &c, mv);
                }
                _ => return (t, ty),
            }
        }
    }

    pub fn check(&mut self, cx: &mut Cx, e: &Expr, expected: &Val, tail: bool) -> Tm {
        let covered = std::mem::take(&mut self.alias_covered);
        // A value the function returns: its postconditions must hold of it (§7.1).
        let returned = tail
            && self.post_target.is_some()
            && !matches!(e.kind, ExprKind::If(..) | ExprKind::Match(..) | ExprKind::Block(..) | ExprKind::Try(_));
        let t = self.check_inner(cx, e, expected, tail);
        let inferred = self.last_inferred.take();
        // A value checked against a refinement alias must satisfy it (D71),
        // unless the call it is passed to, or the function returning it,
        // already checks that alias.
        if !covered && !returned && !matches!(t, Tm::Error) {
            if let Some((d, args)) = self.refined_alias(expected) {
                let already = inferred.as_ref().and_then(|ty| self.refined_alias(ty)).is_some_and(|(d2, _)| d2 == d);
                if !already {
                    let v = self.eval(cx, &t);
                    self.refined_obligation(cx, d, args, v, e.span);
                }
            }
        }
        if returned && !matches!(t, Tm::Error) {
            let v = self.eval(cx, &t);
            self.oblige_posts_at(cx, v, e.span);
        }
        t
    }

    fn check_inner(&mut self, cx: &mut Cx, e: &Expr, expected: &Val, tail: bool) -> Tm {
        let exp = self.force(expected);
        // An implicit Π expected and a non-lambda given: insert an implicit lambda.
        if let Val::Pi(x, m, Icit::Impl, a, c) = &exp {
            let v = Val::var(cx.lvl());
            cx.bind(x, (**a).clone(), *m);
            let body_ty = apply_closure(&self.g, c, v);
            let t = self.check(cx, e, &body_ty, tail);
            cx.pop();
            return Tm::Lam(x.clone(), *m, Icit::Impl, Rc::new(t));
        }
        match (&e.kind, &exp) {
            (ExprKind::Lambda(pats, body), Val::Pi(_, m, Icit::Expl, a, c)) => {
                let map_sub = self.map_elem_sub.take();
                let p = &pats[0];
                let (name, simple) = match &p.kind {
                    ast::PatKind::Var(n) => (n.clone(), true),
                    ast::PatKind::Wild => ("_".to_string(), true),
                    _ => (format!("$arg{}", cx.lvl()), false),
                };
                let v = Val::var(cx.lvl());
                let l = cx.bind(&name, (**a).clone(), *m);
                cx.locals[l].sub = map_sub;
                let body_ty = apply_closure(&self.g, c, v);
                let rest: Expr = if pats.len() > 1 {
                    mk(ExprKind::Lambda(pats[1..].to_vec(), body.clone()), e.span)
                } else {
                    (**body).clone()
                };
                // A lambda's results are not the function's.
                let saved_post = self.post_target.take();
                let t = if simple {
                    self.check(cx, &rest, &body_ty, true)
                } else {
                    let scrut = mk(ExprKind::Var(name.clone()), p.span);
                    let arm = vec![(p.clone(), None, ArmBody::Expr(&rest))];
                    self.elab_match(cx, &scrut, arm, Some(&body_ty), true, e.span).0
                };
                self.post_target = saved_post;
                cx.pop();
                Tm::Lam(Rc::from(name.as_str()), *m, Icit::Expl, Rc::new(t))
            }
            (ExprKind::If(c, t, f), _) => {
                let b = self.bool_ty();
                let ct = self.check(cx, c, &b, false);
                let cv = self.eval(cx, &ct);
                let saved = cx.facts.len();
                cx.assume(self.is_bool(cv.clone(), true));
                let tt = self.check(cx, t, &exp, tail);
                cx.facts.truncate(saved);
                cx.assume(self.is_bool(cv, false));
                let ft = self.check(cx, f, &exp, tail);
                cx.facts.truncate(saved);
                self.if_tm(ct, tt, ft)
            }
            (ExprKind::Match(s, arms), _) => {
                let arms_in = arms.iter().map(|a| (a.pat.clone(), a.guard.as_ref(), ArmBody::Expr(&a.body))).collect();
                self.elab_match(cx, s, arms_in, Some(&exp), tail, e.span).0
            }
            (ExprKind::Block(b), _) => self.check_block(cx, b, &exp, tail),
            (ExprKind::Try(x), _) => {
                if !tail {
                    self.try_not_tail(e.span);
                }
                self.check(cx, x, &exp, tail)
            }
            (ExprKind::Lit(ast::Lit::Int(s)), Val::TyCon(id, _))
                if Some(*id) == self.g.well_known.nat || Some(*id) == self.g.well_known.int =>
            {
                Tm::Lit(Lit::Num(self.number(s, e.span)))
            }
            (ExprKind::Lit(ast::Lit::Int(_)), Val::TyCon(..) | Val::TupleTy(_) | Val::Pi(..)) => {
                let shown = self.show_val(cx, &exp);
                self.err(
                    Diagnostic::error("E0201", format!("type mismatch: expected `{shown}`, found a number"), e.span)
                        .with_label(format!("this is a number, not a `{shown}`")),
                );
                Tm::Error
            }
            (ExprKind::Binary(op, l, r), Val::TyCon(..))
                if matches!(op, Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Rem | Op::Concat) =>
            {
                // The result has the operands' type, so check both against it.
                let lt = self.check_operand(cx, l, &exp);
                let rt = self.check_operand(cx, r, &exp);
                self.finish_arith(cx, *op, lt, rt, exp.clone(), l.span.to(r.span), e.span).0
            }
            (ExprKind::Binary(Op::Cons, l, r), Val::TyCon(id, args)) if Some(*id) == self.g.well_known.list => {
                // Checked, so that the element type is the expected one (D71).
                let elem = args[0].clone();
                let lt = self.check(cx, l, &elem, false);
                let rt = self.check(cx, r, &exp, false);
                let et = quote(&self.g, cx.lvl(), &elem);
                match self.g.well_known.cons {
                    Some(c) => Tm::ConApp(c, vec![et, lt, rt]),
                    None => Tm::Error,
                }
            }
            (ExprKind::List(items), Val::TyCon(id, args)) if Some(*id) == self.g.well_known.list => {
                let elem = args[0].clone();
                let ts: Vec<Tm> = items.iter().map(|it| self.check(cx, it, &elem, false)).collect();
                self.list_tm(cx, &elem, ts)
            }
            (ExprKind::Tuple(items), Val::TupleTy(tys)) if items.len() == tys.len() => {
                let ts = items.iter().zip(tys.clone()).map(|(it, t)| self.check(cx, it, &t, false)).collect();
                Tm::Tuple(ts)
            }
            (ExprKind::Tuple(items), Val::Univ(_)) => {
                Tm::TupleTy(items.iter().map(|it| self.elab_type(cx, it)).collect())
            }
            (ExprKind::Unit, Val::Univ(_)) => Tm::TupleTy(vec![]),
            _ => {
                if matches!(e.kind, ExprKind::App(..)) && self.has_refined(cx, expected, 0) {
                    self.app_expected = Some(expected.clone());
                }
                let (t, ty) = self.infer(cx, e);
                self.app_expected = None;
                if !self.unify_at(cx, &exp, &ty, e.span, "this expression") {
                    return Tm::Error;
                }
                // A refinement inside a type argument is never gained (D71).
                if let Some(g) = self.refined_mismatch(cx, expected, &ty, e.span) {
                    self.report_gained(cx, expected, &ty, &g, e.span, "this expression");
                    return Tm::Error;
                }
                self.last_inferred = Some(ty);
                t
            }
        }
    }

    pub fn infer(&mut self, cx: &mut Cx, e: &Expr) -> (Tm, Val) {
        match &e.kind {
            ExprKind::Var(n) => {
                let (t, ty) = self.infer_var(cx, n, e.span);
                if self.in_app_head {
                    return (t, ty);
                }
                // A function with a specification, as a value (D85).
                let ty = self.refined_fn_type(cx, &t, ty);
                (t, ty)
            }
            ExprKind::Con(n) => match self.resolve(n, cx.type_pos) {
                Some(s) => {
                    let (t, ty) = self.sym_term(cx, s, e.span);
                    self.insert(cx, t, ty)
                }
                None => {
                    self.err(Diagnostic::error("E0204", format!("unknown name `{n}`"), e.span).with_label("not found"));
                    (Tm::Error, Val::Error)
                }
            },
            ExprKind::Lit(l) => self.infer_lit(cx, l, e.span),
            ExprKind::Unit => {
                if cx.type_pos {
                    (Tm::TupleTy(vec![]), Val::Univ(0))
                } else {
                    (Tm::Tuple(vec![]), self.unit())
                }
            }
            ExprKind::Tuple(items) => {
                let mut ts = Vec::new();
                let mut tys = Vec::new();
                for it in items {
                    let (t, ty) = self.infer(cx, it);
                    ts.push(t);
                    tys.push(ty);
                }
                if tys.iter().all(|t| matches!(self.force(t), Val::Univ(_))) {
                    (Tm::TupleTy(ts), Val::Univ(0))
                } else {
                    (Tm::Tuple(ts), Val::TupleTy(tys))
                }
            }
            ExprKind::List(items) => {
                let elem = if let Some(first) = items.first() {
                    let (_, ty) = self.infer(cx, first);
                    ty
                } else {
                    self.fresh_meta_val(cx)
                };
                let ts: Vec<Tm> = items.iter().map(|it| self.check(cx, it, &elem, false)).collect();
                let t = self.list_tm(cx, &elem, ts);
                (t, self.ty_val(self.g.well_known.list, vec![elem]))
            }
            ExprKind::App(..) => self.elab_app(cx, e),
            ExprKind::Binary(op, l, r) => self.elab_binary(cx, *op, l, r, e.span),
            ExprKind::Refine(r) => (self.elab_refine(cx, r), Val::Univ(0)),
            ExprKind::Arrow(a, b) => {
                let at = self.elab_type(cx, a);
                let av = self.eval(cx, &at);
                // A function taking a resource takes it exactly once (D39).
                let m = if self.type_linear(&at) { Mult::One } else { Mult::Many };
                cx.bind("_", av, m);
                let bt = self.elab_type(cx, b);
                cx.pop();
                (Tm::Pi(Rc::from("_"), m, Icit::Expl, Rc::new(at), Rc::new(bt)), Val::Univ(0))
            }
            ExprKind::Neg(x) => {
                let int = self.int();
                if let ExprKind::Lit(ast::Lit::Int(s)) = &x.kind {
                    let n = self.number(s, x.span);
                    return (Tm::Lit(Lit::Num(-n)), int);
                }
                let t = self.check(cx, x, &int, false);
                (Tm::PrimApp(Prim::Neg, vec![t]), int)
            }
            ExprKind::OpRef(op) => {
                let a = format!("$a{}", cx.lvl());
                let b = format!("$b{}", cx.lvl());
                let body = mk(
                    ExprKind::Binary(*op, Box::new(mk(ExprKind::Var(a.clone()), e.span)), Box::new(mk(ExprKind::Var(b.clone()), e.span))),
                    e.span,
                );
                let lam = mk(ExprKind::Lambda(vec![pvar(&a, e.span), pvar(&b, e.span)], Box::new(body)), e.span);
                self.infer(cx, &lam)
            }
            ExprKind::SectionL(op, x) => {
                let b = format!("$b{}", cx.lvl());
                let body = mk(ExprKind::Binary(*op, x.clone(), Box::new(mk(ExprKind::Var(b.clone()), e.span))), e.span);
                let lam = mk(ExprKind::Lambda(vec![pvar(&b, e.span)], Box::new(body)), e.span);
                self.infer(cx, &lam)
            }
            ExprKind::SectionR(op, x) => {
                let a = format!("$a{}", cx.lvl());
                let body = mk(ExprKind::Binary(*op, Box::new(mk(ExprKind::Var(a.clone()), e.span)), x.clone()), e.span);
                let lam = mk(ExprKind::Lambda(vec![pvar(&a, e.span)], Box::new(body)), e.span);
                self.infer(cx, &lam)
            }
            ExprKind::Field(x, name) => self.elab_field(cx, x, name, e.span),
            ExprKind::Index(a, i) => {
                let bytes = self.bytes();
                let nat = self.nat();
                let at = self.check(cx, a, &bytes, false);
                let it = self.check(cx, i, &nat, false);
                let (av, iv) = (self.eval(cx, &at), self.eval(cx, &it));
                let goal = Self::prim_val(Prim::Lt, vec![iv, Self::prim_val(Prim::Len, vec![av])]);
                let text = format!("{} < len {}", self.src_text(i.span), self.src_text(a.span));
                self.oblige(cx, e.span, ObKind::Index, text, goal, None);
                (Tm::PrimApp(Prim::Index, vec![at, it]), nat)
            }
            ExprKind::Lambda(pats, body) => {
                // Infer a lambda: parameter types are unknowns.
                let mut binders = Vec::new();
                let start = cx.lvl();
                for p in pats {
                    let name = match &p.kind {
                        ast::PatKind::Var(n) => n.clone(),
                        ast::PatKind::Wild => "_".to_string(),
                        _ => {
                            // Delegate complex parameter patterns to checking mode.
                            cx.truncate(start);
                            let mv = self.fresh_meta_val(cx);
                            let t = self.check(cx, e, &mv, true);
                            return (t, mv);
                        }
                    };
                    let a = self.fresh_meta_val(cx);
                    let at = quote(&self.g, cx.lvl(), &a);
                    cx.bind(&name, a, Mult::Many);
                    binders.push((Rc::<str>::from(name.as_str()), at));
                }
                let (bt, bty) = self.infer(cx, body);
                let bty_t = quote(&self.g, cx.lvl(), &bty);
                cx.truncate(start);
                let mut t = bt;
                let mut ty = bty_t;
                for (n, a) in binders.into_iter().rev() {
                    t = Tm::Lam(n.clone(), Mult::Many, Icit::Expl, Rc::new(t));
                    ty = Tm::Pi(n, Mult::Many, Icit::Expl, Rc::new(a), Rc::new(ty));
                }
                let tyv = self.eval(cx, &ty);
                (t, tyv)
            }
            ExprKind::If(..) | ExprKind::Match(..) | ExprKind::Block(..) | ExprKind::Try(..) => {
                let mv = self.fresh_meta_val(cx);
                let t = self.check(cx, e, &mv, false);
                (t, mv)
            }
            ExprKind::Par(items) => {
                let tuple = mk(ExprKind::Tuple(items.clone()), e.span);
                let (t, ty) = self.infer(cx, &tuple);
                (Tm::PrimApp(Prim::Par, vec![t]), ty)
            }
            ExprKind::Fork(..) | ExprKind::Join(..) => self.elab_fork_join(cx, e),
            ExprKind::Auto | ExprKind::Admit => match self.proof_goal.clone() {
                // In a proof: `auto` proves the goal from the facts in scope; `admit` assumes it (D49).
                Some((goal, text)) => {
                    if matches!(e.kind, ExprKind::Auto) {
                        let name = self.cur_fn.map(|d| self.g.defs[d.0 as usize].name.to_string()).unwrap_or_default();
                        let _ = name;
                        self.oblige(cx, e.span, ObKind::Auto, text, goal, None);
                    } else {
                        self.admits.push(Trusted { module: self.cur.clone(), span: e.span, what: format!("admit: {text}") });
                    }
                    (Tm::Tuple(vec![]), self.unit())
                }
                None => {
                    self.err(Diagnostic::error("E0212", "`auto` and `admit` are only allowed in proofs", e.span));
                    (Tm::Error, Val::Error)
                }
            },
            ExprKind::Error => (Tm::Error, Val::Error),
        }
    }

    // ── names ───────────────────────────────────────────────────────────────

    fn infer_var(&mut self, cx: &mut Cx, n: &str, span: Span) -> (Tm, Val) {
        if let Some(l) = cx.lookup(n) {
            let ty = cx.locals[l].ty.clone();
            if self.map_elem_sub.is_some() {
                self.map_elem_sub = None;
            }
            return (cx.var(l), ty);
        }
        if n == "__builtin" {
            // In a standard-library proof: an axiom about a primitive (D56).
            if self.stdlib_mode {
                if let Some((_, text)) = self.proof_goal.clone() {
                    if let Some(d) = self.cur_fn {
                        self.axiom_defs.insert(d);
                    }
                    let _ = text;
                    return (Tm::Tuple(vec![]), self.unit());
                }
            }
            self.err(Diagnostic::error("E0356", "`__builtin` bodies are only allowed in the standard library", span));
            return (Tm::Error, Val::Error);
        }
        match self.resolve(n, cx.type_pos) {
            Some(s) => {
                if let Sym::Def(d) = s {
                    self.note_reference(d, span);
                    if !self.in_app_head && !self.g.defs[d.0 as usize].comptime.is_empty() {
                        self.err(
                            Diagnostic::error("E0271", format!("`{n}` is a compile-time function, so it must be called with all its arguments"), span)
                                .with_help("it is expanded where it is called (D59); wrap the call in a lambda to pass it as a value, e.g. `\\x -> f 2 x`"),
                        );
                    }
                }
                let (t, ty) = self.sym_term(cx, s, span);
                self.insert(cx, t, ty)
            }
            None => {
                if self.qualifier(n).is_some() {
                    self.err(
                        Diagnostic::error("E0213", format!("`{n}` is a module, not a value"), span)
                            .with_help(format!("use one of its exports, e.g. `{n}.name`")),
                    );
                } else if crate::elab::stdlib::source(&format!("std.{n}")).is_some() {
                    self.err(
                        Diagnostic::error("E0204", format!("unknown name `{n}`"), span)
                            .with_help(format!("`{n}` is a standard library module; add `import std.{n}`")),
                    );
                } else {
                    self.err(Diagnostic::error("E0204", format!("unknown name `{n}`"), span).with_label("not found"));
                }
                (Tm::Error, Val::Error)
            }
        }
    }

    /// Record a reference to a definition of this module (for termination).
    fn note_reference(&mut self, d: DefId, span: Span) {
        let Some(caller) = self.cur_fn else { return };
        if self.g.defs[d.0 as usize].module.as_ref() != self.cur {
            return;
        }
        let args = match self.map_elem_sub.take() {
            Some(p) => vec![Some(p)],
            None => vec![],
        };
        self.calls.push(CallRec { caller, callee: d, args, span });
    }

    pub fn sym_term(&mut self, _cx: &Cx, s: Sym, span: Span) -> (Tm, Val) {
        let empty = Rc::new(Vec::new());
        match s {
            Sym::Def(d) => {
                let ty = self.g.defs[d.0 as usize].ty.clone();
                if matches!(ty, Tm::Error) && self.g.defs[d.0 as usize].body.is_none() {
                    // Only in a cycle, which E0225 reports (D65).
                    return (Tm::Error, Val::Error);
                }
                (Tm::Def(d), eval(&self.g, &empty, &ty))
            }
            Sym::Ty(t) => {
                let params = self.g.tys[t.0 as usize].params.clone();
                let ty = Elab::pi_of(
                    &params.iter().map(|(n, ty)| (n.clone(), Mult::Many, Icit::Expl, ty.clone())).collect::<Vec<_>>(),
                    Tm::Univ(0),
                );
                (Tm::TyCon(t), eval(&self.g, &empty, &ty))
            }
            Sym::Con(c) => {
                let ty = self.con_type(c);
                (Tm::Con(c), eval(&self.g, &empty, &ty))
            }
            Sym::Univ => (Tm::Univ(0), Val::Univ(1)),
            Sym::Len | Sym::Format => {
                let name = if s == Sym::Len { "len" } else { "format" };
                self.err(Diagnostic::error(
                    "E0214",
                    format!("`{name}` must be applied to an argument here, e.g. `{name} x`"),
                    span,
                ));
                (Tm::Error, Val::Error)
            }
        }
    }

    /// Π (params, implicit, erased) (fields) → T params
    pub fn con_type(&self, c: ConId) -> Tm {
        let ci = &self.g.cons[c.0 as usize];
        let ti = &self.g.tys[ci.ty.0 as usize];
        let np = ti.params.len();
        let nf = ci.fields.len();
        let mut binders: Vec<(Name, Mult, Icit, Tm)> =
            ti.params.iter().map(|(n, t)| (n.clone(), Mult::Zero, Icit::Impl, t.clone())).collect();
        binders.extend(ci.fields.iter().map(|(n, m, i, t)| (n.clone(), *m, *i, t.clone())));
        let res = Tm::TyConApp(ci.ty, (0..np).map(|p| Tm::Var(np + nf - 1 - p)).collect());
        Elab::pi_of(&binders, res)
    }

    fn infer_lit(&mut self, cx: &mut Cx, l: &ast::Lit, span: Span) -> (Tm, Val) {
        match l {
            ast::Lit::Int(s) => {
                let n = self.number(s, span);
                let mv = self.fresh_meta_val(cx);
                self.deferred.push(Deferred {
                    ty: mv.clone(),
                    kind: OpClass::Numeric,
                    span,
                    what: "a number literal".into(),
                    lvl: cx.lvl(),
                    names: cx.names(),
                });
                (Tm::Lit(Lit::Num(n)), mv)
            }
            ast::Lit::Byte(b) => (Tm::Lit(Lit::Num(*b as i128)), self.nat()),
            ast::Lit::Char(c) => (Tm::Lit(Lit::Num(*c as i128)), self.nat()),
            ast::Lit::Str(s) => (Tm::Lit(Lit::Str(Rc::from(s.as_str()))), self.string()),
            ast::Lit::Bytes(b) => (Tm::Lit(Lit::Bytes(Rc::from(b.as_slice()))), self.bytes()),
        }
    }

    pub fn list_tm(&mut self, cx: &Cx, elem: &Val, items: Vec<Tm>) -> Tm {
        let (Some(nil), Some(cons)) = (self.g.well_known.nil, self.g.well_known.cons) else { return Tm::Error };
        let et = quote(&self.g, cx.lvl(), elem);
        let mut t = Tm::ConApp(nil, vec![et.clone()]);
        for it in items.into_iter().rev() {
            t = Tm::ConApp(cons, vec![et.clone(), it, t]);
        }
        t
    }

    pub fn if_tm(&self, c: Tm, t: Tm, f: Tm) -> Tm {
        let (Some(tc), Some(fc)) = (self.g.well_known.true_con, self.g.well_known.false_con) else { return Tm::Error };
        Tm::Case(Rc::new(c), Rc::new(CaseTm { branches: vec![(fc, 0, f), (tc, 0, t)], lits: vec![], default: None }))
    }

    fn bool_lit(&self, b: bool) -> Tm {
        let c = if b { self.g.well_known.true_con } else { self.g.well_known.false_con };
        c.map(|c| Tm::ConApp(c, vec![])).unwrap_or(Tm::Error)
    }

    // ── application ─────────────────────────────────────────────────────────

    fn elab_app(&mut self, cx: &mut Cx, e: &Expr) -> (Tm, Val) {
        let want = self.app_expected.take();
        let saved_checks = std::mem::replace(&mut self.head_checks_aliases, false);
        let r = self.elab_app_inner(cx, e, want);
        self.head_checks_aliases = saved_checks;
        r
    }

    fn elab_app_inner(&mut self, cx: &mut Cx, e: &Expr, want: Option<Val>) -> (Tm, Val) {
        let mut args: Vec<&Expr> = Vec::new();
        let mut head = e;
        while let ExprKind::App(f, a) = &head.kind {
            args.push(a);
            head = f;
        }
        args.reverse();

        // Overloaded built-ins (D38).
        if let ExprKind::Var(n) = &head.kind {
            if cx.lookup(n).is_none() {
                match self.resolve(n, false) {
                    Some(Sym::Len) => {
                        let (at, aty) = self.infer(cx, args[0]);
                        self.deferred.push(Deferred {
                            ty: aty,
                            kind: OpClass::HasLen,
                            span: args[0].span,
                            what: "`len`".into(),
                            lvl: cx.lvl(),
                            names: cx.names(),
                        });
                        let r = (Tm::PrimApp(Prim::Len, vec![at]), self.nat());
                        return self.apply_rest(cx, r, &args[1..], e.span);
                    }
                    Some(Sym::Format) => {
                        let (at, _) = self.infer(cx, args[0]);
                        let r = (Tm::PrimApp(Prim::Format, vec![at]), self.string());
                        return self.apply_rest(cx, r, &args[1..], e.span);
                    }
                    _ => {}
                }
            }
        }

        // `map f xs` where xs is a structural subterm: f's argument is too (Lean's `attach`).
        let is_map = self.is_list_map(cx, head);
        let ncalls = self.calls.len();
        let saved_head = std::mem::replace(&mut self.in_app_head, true);
        let (ft, fty) = self.infer(cx, head);
        self.in_app_head = saved_head;
        let head_call = (self.calls.len() == ncalls + 1 && matches!(head.kind, ExprKind::Var(_))).then_some(ncalls);
        if let Some(i) = head_call {
            let classified: Vec<Option<usize>> = args.iter().map(|a| self.subterm_of(cx, a)).collect();
            self.calls[i].args = classified;
        }
        let map_sub = if is_map && args.len() >= 2 { self.subterm_of_or_param(cx, args[1]) } else { None };
        self.head_checks_aliases = match &ft {
            Tm::Def(d) => self.specs.get(d).is_some_and(|s| s.preds.iter().any(|p| p.alias.is_some() && !p.is_post)),
            Tm::Con(c) => self.con_invs.contains_key(c),
            _ => false,
        };
        let (ft, fty) = match want {
            Some(w) => self.presolve_result(cx, ft, fty, args.len(), &w),
            None => (ft, fty),
        };
        let (ft, fty) = self.look_ahead(cx, ft, fty, &args);
        let mut t = ft;
        let mut ty = fty;
        let head_text = self.src_text(head.span);
        let saved_arg_of = self.arg_of.replace(head_text);
        for (k, a) in args.iter().enumerate() {
            if k == 0 {
                self.map_elem_sub = map_sub;
            }
            let (t2, ty2) = self.apply_one(cx, t, ty, a);
            self.map_elem_sub = None;
            t = t2;
            ty = ty2;
        }
        self.arg_of = saved_arg_of;
        let (t, ty) = self.insert(cx, t, ty);
        self.call_obligations(cx, &t, e.span, head.span);
        // A partial application (D86).
        let ty = self.refined_fn_type(cx, &t, ty);
        // A compile-time argument that isn't known: its type may not compute
        // either, so don't also report a mismatch.
        if !self.check_comptime_call(cx, &t, &args, e.span) {
            return (Tm::Error, Val::Error);
        }
        (t, ty)
    }

    /// A call of a function with `comptime` parameters (D59): it must be
    /// complete, and each such argument known at compile time.
    fn check_comptime_call(&mut self, cx: &Cx, t: &Tm, args: &[&Expr], span: Span) -> bool {
        let mut spine = Vec::new();
        let mut h = t;
        while let Tm::App(f, a, _, _) = h {
            spine.push(a.clone());
            h = f;
        }
        spine.reverse();
        let Tm::Def(d) = h else { return true };
        let ct = self.g.defs[d.0 as usize].comptime.clone();
        if ct.is_empty() {
            return true;
        }
        let mut ok = true;
        let name = self.g.defs[d.0 as usize].name.to_string();
        let n_implicit = self.fn_meta.get(d).map(|m| m.n_implicit).unwrap_or(0);
        let mut arity = 0;
        let mut ty = self.g.defs[d.0 as usize].ty.clone();
        while let Tm::Pi(_, _, _, _, b) = ty {
            arity += 1;
            ty = (*b).clone();
        }
        for b in ct {
            let Some(arg) = spine.get(b).filter(|_| spine.len() >= arity) else {
                self.err(
                    Diagnostic::error("E0271", format!("`{name}` is a compile-time function, so it must be called with all its arguments"), span)
                        .with_help("it is expanded where it is called (D59); wrap the call in a lambda to pass it as a value, e.g. `\\x -> f 2 x`"),
                );
                return false;
            };
            if !self.tm_static(cx, arg, 0, cx.lvl()) {
                let pname = self.fn_meta.get(d).and_then(|m| m.params.get(b.saturating_sub(n_implicit))).map(|p| p.0.clone()).unwrap_or_default();
                let at = args.get(b.saturating_sub(n_implicit)).map(|a| a.span).unwrap_or(span);
                self.err(
                    Diagnostic::error("E0270", format!("`{pname}` of `{name}` must be known at compile time"), at)
                        .with_label("this depends on a value only known when the program runs")
                        .with_help("pass a literal, a constant, or a `comptime` parameter of the calling function"),
                );
                ok = false;
            }
        }
        ok
    }

    /// Preconditions of a call and invariants of a constructor application (§7.1).
    fn call_obligations(&mut self, cx: &Cx, t: &Tm, span: Span, head_span: Span) {
        let mut args = Vec::new();
        let mut h = t;
        while let Tm::App(f, a, _, _) = h {
            args.push(a.clone());
            h = f;
        }
        args.reverse();
        match h {
            Tm::Def(d) => {
                let Some(spec) = self.specs.get(d).cloned() else { return };
                if args.len() >= spec.n_binders {
                    let env: Vec<Val> = args[..spec.n_binders].iter().map(|a| self.eval(cx, a)).collect();
                    self.measure_obligation(cx, *d, &env, span, head_span);
                }
                if !spec.preds.iter().any(|p| !p.is_post) {
                    return;
                }
                let name = self.g.defs[d.0 as usize].name.to_string();
                if args.len() < spec.n_binders {
                    // A partial application (D86): preconditions about the
                    // arguments given are checked here; the others are in
                    // its type (`refined_fn_type`).
                    let given = args.len();
                    let total = spec.n_binders + 1;
                    let now = spec.preds.iter().filter(|p| !p.is_post && !mentions_level_from(&p.tm, total, given, 0));
                    let mut env: Vec<Val> = args.iter().map(|a| self.eval(cx, a)).collect();
                    for k in given..total {
                        env.push(Val::var(usize::MAX / 2 + k));
                    }
                    for p in now {
                        let goal = self.inst_pred(p, env.clone());
                        self.oblige(cx, span, ObKind::Pre { callee: name.clone() }, p.text.clone(), goal, None);
                    }
                    return;
                }
                let mut env: Vec<Val> = args[..spec.n_binders].iter().map(|a| self.eval(cx, a)).collect();
                env.push(self.eval(cx, t));
                for p in spec.preds.iter().filter(|p| !p.is_post) {
                    let goal = self.inst_pred(p, env.clone());
                    self.oblige(cx, span, ObKind::Pre { callee: name.clone() }, p.text.clone(), goal, None);
                }

            }
            Tm::Con(c) => {
                let Some(invs) = self.con_invs.get(c).cloned() else { return };
                if args.len() < self.g.arity_con(*c) {
                    return;
                }
                let env: Vec<Val> = args.iter().map(|a| self.eval(cx, a)).collect();
                let name = self.g.cons[c.0 as usize].name.to_string();
                for p in &invs {
                    let goal = self.inst_pred(p, env.clone());
                    self.oblige(cx, span, ObKind::Invariant { con: name.clone() }, p.text.clone(), goal, None);
                }
            }
            _ => {}
        }
    }

    /// A call of `callee` from a function with a measure: the callee's measure at
    /// the arguments must be lexicographically below the caller's (§5.3).
    /// Kept only if both turn out to be in one recursive group.
    fn measure_obligation(&mut self, cx: &Cx, callee: DefId, args: &[Val], span: Span, head_span: Span) {
        self.saturated_heads.insert(head_span);
        let Some(caller) = self.cur_fn else { return };
        let (Some(cs), Some(ks)) = (self.specs.get(&caller).cloned(), self.specs.get(&callee).cloned()) else { return };
        let (Some((mine, text)), Some((theirs, _))) = (cs.measure, ks.measure) else { return };
        if mine.len() != theirs.len() || self.in_spec > 0 {
            return;
        }
        let here_env = Rc::new((0..cs.n_binders).map(Val::var).collect::<Vec<_>>());
        let there_env = Rc::new(args.to_vec());
        let lvl = cx.lvl();
        let a: Vec<Tm> = theirs.iter().map(|t| quote(&self.g, lvl, &eval(&self.g, &there_env, t))).collect();
        let b: Vec<Tm> = mine.iter().map(|t| quote(&self.g, lvl, &eval(&self.g, &here_env, t))).collect();
        // (a1, …) < (b1, …): a1 < b1, or a1 == b1 and the rest is smaller.
        let mut goal = Tm::PrimApp(Prim::Lt, vec![a[a.len() - 1].clone(), b[b.len() - 1].clone()]);
        for k in (0..a.len() - 1).rev() {
            let lt = Tm::PrimApp(Prim::Lt, vec![a[k].clone(), b[k].clone()]);
            let eq = Tm::PrimApp(Prim::Eq, vec![a[k].clone(), b[k].clone()]);
            let rest = self.if_tm(eq, goal, self.bool_lit(false));
            goal = self.if_tm(lt, self.bool_lit(true), rest);
        }
        let goal = self.eval(cx, &goal);
        let func = self.g.defs[caller.0 as usize].name.to_string();
        let n = self.obligations.len();
        self.oblige(cx, span, ObKind::Measure { func, measure: text.clone() }, text, goal, None);
        if self.obligations.len() > n {
            let ob = self.obligations.pop().expect("just pushed");
            self.measure_obs.push((caller, callee, ob));
        }
    }

    /// `have e` (D49): a lemma's conclusion, or a proven `Bool`, becomes a fact.
    pub fn have(&mut self, cx: &mut Cx, e: &Expr) {
        let (t, ty) = self.infer(cx, e);
        let mut h = &t;
        while let Tm::App(f, ..) = h {
            h = f;
        }
        if let Tm::Def(d) = h {
            if let Some(spec) = self.specs.get(d).cloned() {
                if let Some(ens) = &spec.ensures {
                    let mut args = Vec::new();
                    let mut x = &t;
                    while let Tm::App(f, a, _, _) = x {
                        args.push(a.clone());
                        x = f;
                    }
                    args.reverse();
                    if args.len() < spec.n_binders {
                        let name = self.g.defs[d.0 as usize].name.to_string();
                        self.err(
                            Diagnostic::error("E0454", format!("`have {name}` needs all of the lemma's arguments"), e.span)
                                .with_help("pass every parameter of the lemma"),
                        );
                        return;
                    }
                    let mut env: Vec<Val> = args[..spec.n_binders].iter().map(|a| self.eval(cx, a)).collect();
                    for l in &spec.lets {
                        let v = eval(&self.g, &Rc::new(env.clone()), l);
                        env.push(v);
                    }
                    let fact = self.inst_pred(ens, env);
                    cx.assume(fact);
                    // Using a fact about a primitive: listed in the ledger (D56).
                    if self.axiom_defs.contains(d) {
                        let info = &self.g.defs[d.0 as usize];
                        let what = format!("builtin axiom {}.{}", info.module, info.name);
                        self.builtin_axioms.push(Trusted { module: self.cur.clone(), span: e.span, what });
                    }
                    return;
                }
            }
        }
        let b = self.bool_ty();
        if !self.unify_at(cx, &b, &ty, e.span, "`have`") {
            return;
        }
        let v = self.eval(cx, &t);
        let text = self.src_text(e.span);
        self.oblige(cx, e.span, ObKind::Have, text, v.clone(), None);
        cx.assume(v);
    }

    fn apply_rest(&mut self, cx: &mut Cx, r: (Tm, Val), args: &[&Expr], _span: Span) -> (Tm, Val) {
        let (mut t, mut ty) = r;
        for a in args {
            let (t2, ty2) = self.apply_one(cx, t, ty, a);
            t = t2;
            ty = ty2;
        }
        (t, ty)
    }

    /// Apply `t : ty` to one explicit argument.
    /// Unify the result type of applying `t` to `n` explicit arguments with
    /// the expected type before the arguments are checked, when it doesn't
    /// depend on them: `n :: xs` against `List Small` makes the element type
    /// `Small`, so `n` is checked against it (D71).
    fn presolve_result(&mut self, cx: &Cx, t: Tm, ty: Val, n: usize, want: &Val) -> (Tm, Val) {
        let (t, ty) = self.insert(cx, t, ty);
        let mut r = ty.clone();
        for k in 0..n {
            match self.force(&r) {
                Val::Pi(_, _, Icit::Expl, _, c) => r = apply_closure(&self.g, &c, Val::var(cx.lvl() + k)),
                _ => return (t, ty),
            }
        }
        if matches!(self.force(&r), Val::Pi(_, _, Icit::Impl, _, _)) {
            return (t, ty);
        }
        let q = quote(&self.g, cx.lvl() + n, &r);
        if !mentions_level_from(&q, cx.lvl() + n, cx.lvl(), 0) {
            let _ = unify(&self.g, cx.lvl(), want, &r);
        }
        (t, ty)
    }

    /// A function argument followed by a local variable (`map (\x -> …) xs`,
    /// `map sub5 xs`): take the variable's type first, so the function is
    /// checked against the most precise type (`Small`, not `Nat`; D71, D87).
    /// Looking up a local has no effects, so nothing is elaborated twice.
    fn look_ahead(&mut self, cx: &Cx, t: Tm, ty: Val, args: &[&Expr]) -> (Tm, Val) {
        let (t, ty) = self.insert(cx, t, ty);
        let mut r = ty.clone();
        let mut first_fn = None;
        for (k, a) in args.iter().enumerate() {
            let Val::Pi(_, _, Icit::Expl, dom, c) = self.force(&r) else { break };
            if first_fn.is_none() && (matches!(a.kind, ExprKind::Lambda(..)) || matches!(self.force(&dom), Val::Pi(..))) {
                first_fn = Some(k);
            }
            if first_fn.is_some_and(|f| k > f) {
                if let ExprKind::Var(n) = &a.kind {
                    if let Some(l) = cx.lookup(n) {
                        let q = quote(&self.g, cx.lvl() + k, &dom);
                        if !mentions_level_from(&q, cx.lvl() + k, cx.lvl(), 0) {
                            let _ = unify(&self.g, cx.lvl(), &dom, &cx.locals[l].ty.clone());
                        }
                    }
                }
            }
            r = apply_closure(&self.g, &c, Val::var(cx.lvl() + k));
        }
        (t, ty)
    }

    /// An operand of an arithmetic or comparison operator: it takes the
    /// other operand's type, but not its refinement (`x < 10` with `x~Small`
    /// doesn't need `10` to be a `Small`; D71).
    fn check_operand(&mut self, cx: &mut Cx, e: &Expr, ty: &Val) -> Tm {
        self.alias_covered = true;
        self.check(cx, e, ty, false)
    }

    pub fn apply_one(&mut self, cx: &mut Cx, t: Tm, ty: Val, a: &Expr) -> (Tm, Val) {
        let (t, ty) = self.insert(cx, t, ty);
        match self.force(&ty) {
            Val::Pi(_, m, Icit::Expl, dom, c) => {
                // A refined function type's precondition (D84): required to
                // call the function.
                let pre = match self.refined_alias(&dom) {
                    Some((d, args)) if !self.head_checks_aliases && self.is_direct_alias(&dom) && is_anon_alias(&self.g, d) => Some((d, args)),
                    _ => None,
                };
                self.alias_covered = (self.head_checks_aliases && self.is_direct_alias(&dom)) || pre.is_some();
                let at = self.check(cx, a, &dom, false);
                let av = self.eval(cx, &at);
                if let Some((d, args)) = pre {
                    let callee = self.arg_of.clone().unwrap_or_else(|| "the function".into());
                    for p in self.alias_preds.get(&d).cloned().unwrap_or_default() {
                        let mut env = args.clone();
                        env.push(av.clone());
                        let goal = self.inst_pred(&p, env);
                        self.oblige(cx, a.span, ObKind::Pre { callee: callee.clone() }, p.text.clone(), goal, None);
                    }
                }
                (Tm::App(Rc::new(t), Rc::new(at), Icit::Expl, m), apply_closure(&self.g, &c, av))
            }
            Val::Neutral(Head::Meta(_), _) if self.default_if_numeric(&ty) => self.apply_one(cx, t, ty, a),
            Val::Neutral(Head::Meta(_), sp) => {
                // Refine `?m sp` to `(x~?d sp) -> ?c sp x`. The new metas take the
                // same spine as `?m`, so the solution stays in `?m`'s scope.
                let args: Vec<Val> = sp
                    .iter()
                    .filter_map(|e| if let Elim::App(v, _) = e { Some(v.clone()) } else { None })
                    .collect();
                let d = self.g.fresh_meta();
                let c = self.g.fresh_meta();
                let dom = Val::Neutral(
                    Head::Meta(d),
                    Rc::new(args.iter().map(|v| Elim::App(v.clone(), Icit::Expl)).collect()),
                );
                let mut cod = Tm::Meta(c);
                for v in &args {
                    let vt = quote(&self.g, cx.lvl() + 1, v);
                    cod = Tm::App(Rc::new(cod), Rc::new(vt), Icit::Expl, Mult::Many);
                }
                cod = Tm::App(Rc::new(cod), Rc::new(Tm::Var(0)), Icit::Expl, Mult::Many);
                let pi = Val::Pi(Rc::from("x"), Mult::Many, Icit::Expl, Rc::new(dom.clone()), Closure { env: cx.env(), body: Rc::new(cod) });
                self.unify_at(cx, &pi, &ty, a.span, "the function");
                self.apply_one(cx, t, pi, a)
            }
            Val::Error => {
                let _ = self.infer(cx, a);
                (Tm::Error, Val::Error)
            }
            other => {
                let shown = self.show_val(cx, &other);
                self.err(
                    Diagnostic::error(
                        "E0205",
                        format!("too many arguments: this has type `{shown}`, which is not a function"),
                        a.span,
                    )
                    .with_label("extra argument"),
                );
                (Tm::Error, Val::Error)
            }
        }
    }

    fn is_list_map(&self, cx: &Cx, head: &Expr) -> bool {
        let sym = match &head.kind {
            ExprKind::Var(n) if cx.lookup(n).is_none() => self.resolve(n, false),
            ExprKind::Field(q, n) => match &q.kind {
                ExprKind::Var(q) if cx.lookup(q).is_none() => {
                    self.qualifier(q).and_then(|m| self.resolve_qualified(&m, &n.name, false))
                }
                _ => None,
            },
            _ => None,
        };
        match sym {
            Some(Sym::Def(d)) => {
                let info = &self.g.defs[d.0 as usize];
                info.module.as_ref() == "std.list" && info.name.as_ref() == "map"
            }
            _ => false,
        }
    }

    /// If `a` is a local that is a strict structural subterm of parameter p, return p.
    pub fn subterm_of(&self, cx: &Cx, a: &Expr) -> Option<usize> {
        match &a.kind {
            ExprKind::Var(n) => cx.lookup(n).and_then(|l| cx.locals[l].sub),
            _ => None,
        }
    }

    fn subterm_of_or_param(&self, cx: &Cx, a: &Expr) -> Option<usize> {
        match &a.kind {
            ExprKind::Var(n) => cx.lookup(n).and_then(|l| cx.locals[l].sub),
            _ => None,
        }
    }

    // ── operators ───────────────────────────────────────────────────────────

    fn elab_binary(&mut self, cx: &mut Cx, op: Op, l: &Expr, r: &Expr, span: Span) -> (Tm, Val) {
        match op {
            Op::Dollar => {
                let app = mk(ExprKind::App(Box::new(l.clone()), Box::new(r.clone())), span);
                self.infer(cx, &app)
            }
            Op::Dot => {
                let x = format!("$c{}", cx.lvl());
                let inner = mk(ExprKind::App(Box::new(r.clone()), Box::new(mk(ExprKind::Var(x.clone()), span))), span);
                let body = mk(ExprKind::App(Box::new(l.clone()), Box::new(inner)), span);
                let lam = mk(ExprKind::Lambda(vec![pvar(&x, span)], Box::new(body)), span);
                self.infer(cx, &lam)
            }
            Op::And | Op::Or | Op::Implies => {
                let b = self.bool_ty();
                let lt = self.check(cx, l, &b, false);
                // The right operand is only evaluated when the left one allows it.
                let lv = self.eval(cx, &lt);
                let saved = cx.facts.len();
                cx.assume(self.is_bool(lv, op != Op::Or));
                let rt = self.check(cx, r, &b, false);
                cx.facts.truncate(saved);
                let t = match op {
                    Op::And => self.if_tm(lt, rt, self.bool_lit(false)),
                    Op::Or => self.if_tm(lt, self.bool_lit(true), rt),
                    _ => self.if_tm(lt, rt, self.bool_lit(true)),
                };
                (t, b)
            }
            Op::Cons => {
                let (lt, lty) = self.infer(cx, l);
                let list = self.ty_val(self.g.well_known.list, vec![lty.clone()]);
                let rt = self.check(cx, r, &list, false);
                let et = quote(&self.g, cx.lvl(), &lty);
                match self.g.well_known.cons {
                    Some(c) => (Tm::ConApp(c, vec![et, lt, rt]), list),
                    None => (Tm::Error, Val::Error),
                }
            }
            _ => {
                // Take the operand type from the side that is not a bare number
                // literal, so `1 + "a"` blames `"a"`.
                let (lt, rt, lty) = if matches!(l.kind, ExprKind::Lit(ast::Lit::Int(_)))
                    && !matches!(r.kind, ExprKind::Lit(ast::Lit::Int(_)))
                {
                    let (rt, rty) = self.infer(cx, r);
                    let lt = self.check_operand(cx, l, &rty);
                    (lt, rt, rty)
                } else {
                    let (lt, lty) = self.infer(cx, l);
                    let rt = self.check_operand(cx, r, &lty);
                    (lt, rt, lty)
                };
                self.finish_arith(cx, op, lt, rt, lty, l.span.to(r.span), span)
            }
        }
    }

    /// Build a built-in operator application (D38) on operands of type `lty`.
    #[allow(clippy::too_many_arguments)]
    fn finish_arith(&mut self, cx: &Cx, op: Op, lt: Tm, rt: Tm, lty: Val, operands: Span, span: Span) -> (Tm, Val) {
        {
            {
                let (prim, class, result) = match op {
                    Op::Add => (Prim::Add, Some(OpClass::Numeric), None),
                    Op::Sub => (Prim::Sub, Some(OpClass::Numeric), None),
                    Op::Mul => (Prim::Mul, Some(OpClass::Numeric), None),
                    Op::Div => (Prim::Div, Some(OpClass::Numeric), None),
                    Op::Rem => (Prim::Rem, Some(OpClass::Numeric), None),
                    Op::Lt => (Prim::Lt, Some(OpClass::Ordered), Some(self.bool_ty())),
                    Op::Le => (Prim::Le, Some(OpClass::Ordered), Some(self.bool_ty())),
                    Op::Gt => (Prim::Gt, Some(OpClass::Ordered), Some(self.bool_ty())),
                    Op::Ge => (Prim::Ge, Some(OpClass::Ordered), Some(self.bool_ty())),
                    Op::EqEq => (Prim::Eq, None, Some(self.bool_ty())),
                    Op::Ne => (Prim::Ne, None, Some(self.bool_ty())),
                    Op::Concat => (Prim::Concat, Some(OpClass::Concat), None),
                    _ => unreachable!(),
                };
                if let Some(kind) = class {
                    self.deferred.push(Deferred {
                        ty: lty.clone(),
                        kind,
                        span: operands,
                        what: format!("`{}`", op.as_str()),
                        lvl: cx.lvl(),
                        names: cx.names(),
                    });
                }
                let (lv, rv) = (self.eval(cx, &lt), self.eval(cx, &rt));
                match op {
                    Op::Sub => {
                        let goal = Self::prim_val(Prim::Ge, vec![lv, rv]);
                        let text = self.src_text(span);
                        self.oblige(cx, span, ObKind::NatSub, text, goal, Some(lty.clone()));
                    }
                    Op::Div | Op::Rem => {
                        let zero = Val::Lit(Lit::Num(0));
                        let goal = Self::prim_val(Prim::Ne, vec![rv, zero]);
                        let text = self.src_text(span);
                        self.oblige(cx, span, ObKind::Div, text, goal, None);
                    }
                    _ => {}
                }
                let args = if prim == Prim::Sub {
                    // The runtime and the evaluator need to know whether this is `Nat` subtraction.
                    vec![lt, rt, quote(&self.g, cx.lvl(), &lty)]
                } else {
                    vec![lt, rt]
                };
                (Tm::PrimApp(prim, args), result.unwrap_or(lty))
            }
        }
    }

    // ── fields and qualified names ──────────────────────────────────────────

    fn elab_field(&mut self, cx: &mut Cx, x: &Expr, name: &Ident, span: Span) -> (Tm, Val) {
        if let ExprKind::Var(q) = &x.kind {
            if cx.lookup(q).is_none() {
                if let Some(m) = self.qualifier(q) {
                    return match self.resolve_qualified(&m, &name.name, cx.type_pos) {
                        Some(s) => {
                            if let Sym::Def(d) = s {
                                self.note_reference(d, span);
                            }
                            let (t, ty) = self.sym_term(cx, s, span);
                            self.insert(cx, t, ty)
                        }
                        None => {
                            self.err(Diagnostic::error(
                                "E0206",
                                format!("module `{m}` has no export named `{}`", name.name),
                                name.span,
                            ));
                            (Tm::Error, Val::Error)
                        }
                    };
                }
                if self.resolve(q, false).is_none() && self.module().failed_imports.contains(q.as_str()) {
                    return (Tm::Error, Val::Error);
                }
                if self.resolve(q, false).is_none() && crate::elab::stdlib::source(&format!("std.{q}")).is_some() {
                    self.err(
                        Diagnostic::error("E0204", format!("unknown name `{q}`"), x.span)
                            .with_help(format!("`{q}` is a standard library module; add `import std.{q}`")),
                    );
                    return (Tm::Error, Val::Error);
                }
            }
        }
        let (xt, xty) = self.infer(cx, x);
        match self.force(&xty) {
            Val::TyCon(tid, params) if self.g.tys[tid.0 as usize].is_record => {
                let cid = self.g.tys[tid.0 as usize].ctors[0];
                let fields = self.g.cons[cid.0 as usize].fields.clone();
                let Some(idx) = fields.iter().position(|f| f.0.as_ref() == name.name) else {
                    let names: Vec<String> =
                        fields.iter().filter(|f| f.2 == Icit::Expl).map(|f| format!("`{}`", f.0)).collect();
                    let tname = self.g.tys[tid.0 as usize].name.clone();
                    self.err(
                        Diagnostic::error("E0207", format!("record `{tname}` has no field `{}`", name.name), name.span)
                            .with_help(format!("its fields are {}", names.join(", "))),
                    );
                    return (Tm::Error, Val::Error);
                };
                let xv = self.eval(cx, &xt);
                let mut env: Vec<Val> = params;
                for j in 0..idx {
                    env.push(crate::core::eval(
                        &self.g,
                        &Rc::new(vec![xv.clone()]),
                        &Tm::Field(Rc::new(Tm::Var(0)), cid, j),
                    ));
                }
                let fty = eval(&self.g, &Rc::new(env), &fields[idx].3);
                (Tm::Field(Rc::new(xt), cid, idx), fty)
            }
            Val::Error => (Tm::Error, Val::Error),
            other => {
                let shown = self.show_val(cx, &other);
                self.err(
                    Diagnostic::error("E0207", format!("`{shown}` has no field `{}`", name.name), name.span)
                        .with_label(format!("this is a `{shown}`, not a record")),
                );
                (Tm::Error, Val::Error)
            }
        }
    }

    // ── blocks and statements ───────────────────────────────────────────────

    pub fn block_from(&mut self, cx: &mut Cx, stmts: &[Stmt], result: &Expr, expected: &Val, tail: bool) -> Tm {
        let Some((first, rest)) = stmts.split_first() else {
            return self.check(cx, result, expected, tail);
        };
        match first {
            Stmt::Let(pat, rhs) => {
                if let ExprKind::Try(inner) = &rhs.kind {
                    return self.try_let(cx, pat, inner, rest, result, expected, tail, rhs.span);
                }
                match &pat.kind {
                    ast::PatKind::Var(_) | ast::PatKind::Wild => {
                        let name = match &pat.kind {
                            ast::PatKind::Var(n) => n.clone(),
                            _ => "_".to_string(),
                        };
                        let (t, ty) = self.infer(cx, rhs);
                        if name == "_" && self.val_linear(&ty) {
                            self.report_dropped(cx, &ty, pat.span);
                        }
                        let mult = self.named_mult(cx, &name, &ty, pat.span, Mult::Many);
                        let v = self.eval(cx, &t);
                        let tyt = quote(&self.g, cx.lvl(), &ty);
                        let l = cx.define(&name, ty, v, mult);
                        // `let x = y` keeps y's structural information.
                        if let ExprKind::Var(src) = &rhs.kind {
                            if let Some(sl) = cx.locals[..l].iter().rposition(|x| x.name.as_ref() == src.as_str()) {
                                cx.locals[l].sub = cx.locals[sl].sub;
                            }
                        }
                        let body = self.block_from(cx, rest, result, expected, tail);
                        cx.pop();
                        Tm::Let(Rc::from(name.as_str()), mult, Rc::new(tyt), Rc::new(t), Rc::new(body))
                    }
                    _ => {
                        let arms = vec![(pat.clone(), None, ArmBody::Rest(rest, result))];
                        self.elab_match(cx, rhs, arms, Some(expected), tail, pat.span).0
                    }
                }
            }
            Stmt::Have(h) => {
                let saved = cx.facts.len();
                self.have(cx, h);
                let t = self.block_from(cx, rest, result, expected, tail);
                cx.facts.truncate(saved);
                t
            }
            Stmt::Expr(e) => {
                let unit = self.unit();
                let (t, ty) = self.infer(cx, e);
                // A number is never `Unit`; don't let unification decide that it is.
                let numeric = self.default_if_numeric(&ty);
                if numeric
                    || (!matches!(self.force(&ty), Val::TupleTy(ref v) if v.is_empty())
                        && unify(&self.g, cx.lvl(), &unit, &ty).is_err())
                {
                    let shown = self.show_val(cx, &ty);
                    self.err(
                        Diagnostic::error(
                            "E0215",
                            format!("this line produces a `{shown}`, which would be thrown away"),
                            e.span,
                        )
                        .with_help("only calls returning `Unit` can stand alone; write `let _ = …` to discard a value, or make it the block's last line"),
                    );
                }
                let v = self.eval(cx, &t);
                cx.define("_", unit, v, Mult::Many);
                let body = self.block_from(cx, rest, result, expected, tail);
                cx.pop();
                Tm::Let(Rc::from("_"), Mult::Many, Rc::new(Tm::TupleTy(vec![])), Rc::new(t), Rc::new(body))
            }
            Stmt::Bind(pat, rhs) => self.bind_stmt(cx, pat, rhs, rest, result, expected, tail),
            Stmt::When(w) => {
                let t = self.elab_when(cx, w);
                let unit = self.unit();
                let v = self.eval(cx, &t);
                cx.define("_", unit, v, Mult::Many);
                let body = self.block_from(cx, rest, result, expected, tail);
                cx.pop();
                Tm::Let(Rc::from("_"), Mult::Many, Rc::new(Tm::TupleTy(vec![])), Rc::new(t), Rc::new(body))
            }
        }
    }

    fn try_not_tail(&mut self, span: Span) {
        self.err(
            Diagnostic::error("E0230", "`try` can only be used where the block's value is the function's result", span)
                .with_help("`try` returns the error from the enclosing function; use `match` here instead"),
        );
    }

    #[allow(clippy::too_many_arguments)]
    fn try_let(
        &mut self,
        cx: &mut Cx,
        pat: &ast::Pattern,
        inner: &Expr,
        rest: &[Stmt],
        result: &Expr,
        expected: &Val,
        tail: bool,
        span: Span,
    ) -> Tm {
        if !tail {
            self.try_not_tail(span);
        }
        let (it, ity) = self.infer(cx, inner);
        let wk = self.g.well_known.clone();
        let (ok_con, err_con, payload, is_result) = match self.force(&ity) {
            Val::TyCon(t, args) if Some(t) == wk.result => (wk.ok, wk.err, args, true),
            Val::TyCon(t, args) if Some(t) == wk.option => (wk.some, wk.none, args, false),
            Val::Error => return Tm::Error,
            other => {
                let shown = self.show_val(cx, &other);
                self.err(
                    Diagnostic::error("E0231", format!("`try` needs a `Result` or `Option`, but this is `{shown}`"), inner.span)
                        .with_label(format!("has type `{shown}`")),
                );
                return Tm::Error;
            }
        };
        let (Some(ok_con), Some(err_con)) = (ok_con, err_con) else { return Tm::Error };
        // The enclosing result must be a Result with the same error type (or an Option).
        let ret_payload = self.fresh_meta_val(cx);
        let ret = if is_result {
            self.ty_val(wk.result, vec![ret_payload.clone(), payload[1].clone()])
        } else {
            self.ty_val(wk.option, vec![ret_payload.clone()])
        };
        // Outside tail position E0230 is already reported; the local block's
        // type is not the function's, so don't constrain it.
        if tail && unify(&self.g, cx.lvl(), expected, &ret).is_err() {
            let e = self.show_val(cx, expected);
            let what = if is_result {
                format!("`Result _ {}`", self.show_val(cx, &payload[1]))
            } else {
                "`Option _`".to_string()
            };
            self.err(
                Diagnostic::error(
                    "E0232",
                    format!("`try` returns early with the error, so the result here must be {what}, but it is `{e}`"),
                    span,
                )
                .with_label("returns early from here"),
            );
        }
        // Ok/Some branch: bind the payload, then the pattern.
        let payload_ty = payload[0].clone();
        let okv = format!("$ok{}", cx.lvl());
        let it_val = self.eval(cx, &it);
        let l = cx.bind(&okv, payload_ty, Mult::Many);
        // On this path the value was `Ok x` / `Some x` (§7.1).
        let mut ok_args: Vec<Val> = payload.clone();
        ok_args.push(Val::var(l));
        cx.assume(Self::prim_val(Prim::Eq, vec![it_val, Val::Con(ok_con, ok_args)]));
        let ok_body = match &pat.kind {
            ast::PatKind::Var(_) | ast::PatKind::Wild => {
                let pty = cx.locals[cx.lvl() - 1].ty.clone();
                self.let_pattern(cx, pat, Tm::Var(0), pty, rest, result, expected, tail)
            }
            _ => {
                let scrut = mk(ExprKind::Var(okv.clone()), pat.span);
                let arms = vec![(pat.clone(), None, ArmBody::Rest(rest, result))];
                self.elab_match(cx, &scrut, arms, Some(expected), tail, pat.span).0
            }
        };
        cx.pop();
        // Err/None branch: rebuild the error in the enclosing type.
        let rp = quote(&self.g, cx.lvl(), &ret_payload);
        let (err_n, err_body) = if is_result {
            let et = quote(&self.g, cx.lvl() + 1, &payload[1]);
            let rp1 = quote(&self.g, cx.lvl() + 1, &ret_payload);
            (1, Tm::ConApp(err_con, vec![rp1, et, Tm::Var(0)]))
        } else {
            (0, Tm::ConApp(err_con, vec![rp]))
        };
        // The early return is a value the function returns, too.
        if tail && self.post_target.is_some() {
            let saved = cx.facts.len();
            let it_val = self.eval(cx, &it);
            if is_result {
                let l = cx.bind("$err", payload[1].clone(), Mult::Many);
                let mut args = payload.clone();
                args.push(Val::var(l));
                cx.assume(Self::prim_val(Prim::Eq, vec![it_val, Val::Con(err_con, args)]));
                let v = self.eval(cx, &err_body);
                self.oblige_posts_at(cx, v, span);
                cx.pop();
            } else {
                cx.assume(Self::prim_val(Prim::Eq, vec![it_val, Val::Con(err_con, vec![payload[0].clone()])]));
                let v = self.eval(cx, &err_body);
                self.oblige_posts_at(cx, v, span);
            }
            cx.facts.truncate(saved);
        }
        let (ok_n, ok_first) = (1, true);
        let _ = ok_first;
        let mut branches = vec![(ok_con, ok_n, ok_body), (err_con, err_n, err_body)];
        branches.sort_by_key(|b| self.g.cons[b.0 .0 as usize].tag);
        Tm::Case(Rc::new(it), Rc::new(CaseTm { branches, lits: vec![], default: None }))
    }

    #[allow(clippy::too_many_arguments)]
    fn bind_stmt(
        &mut self,
        cx: &mut Cx,
        pat: &ast::Pattern,
        rhs: &Expr,
        rest: &[Stmt],
        result: &Expr,
        expected: &Val,
        tail: bool,
    ) -> Tm {
        // `f <- fork …` / `r <- join …`: bind the future.
        if matches!(rhs.kind, ExprKind::Fork(..) | ExprKind::Join(..)) {
            let (t, ty) = self.elab_fork_join(cx, rhs);
            return self.let_pattern(cx, pat, t, ty, rest, result, expected, tail);
        }
        // `x <- f a r`: r must be a local variable passed last.
        let last = match &rhs.kind {
            ExprKind::App(_, a) => match &a.kind {
                ExprKind::Var(n) => cx.lookup(n).map(|l| (n.clone(), l)),
                _ => None,
            },
            _ => None,
        };
        let Some((rname, rlvl)) = last else {
            self.err(
                Diagnostic::error("E0233", "`<-` needs a call whose last argument is a resource variable", rhs.span)
                    .with_help("write `x <- files.read_line f`, where `f` is an `own` resource; for ordinary values use `let`"),
            );
            return Tm::Error;
        };
        let (t, ty) = self.infer(cx, rhs);
        let rty = cx.locals[rlvl].ty.clone();
        let comps = match self.force(&ty) {
            Val::TupleTy(v) if v.len() == 2 => v,
            Val::Error => return Tm::Error,
            other => {
                let shown = self.show_val(cx, &other);
                self.err(
                    Diagnostic::error(
                        "E0234",
                        format!("`<-` needs a call that returns `(result, {rname})`, but this returns `{shown}`"),
                        rhs.span,
                    )
                    .with_help("operations on authority capabilities (`fs`, `term`, …) return just their result: use `let`"),
                );
                return Tm::Error;
            }
        };
        self.unify_at(cx, &rty, &comps[1], rhs.span, "the returned resource");
        let mult = cx.locals[rlvl].mult;
        // let $t = rhs; let r = $t.1; let pat = $t.0; rest
        let tname = format!("$t{}", cx.lvl());
        let tv = self.eval(cx, &t);
        let tyt = quote(&self.g, cx.lvl(), &ty);
        cx.define(&tname, ty.clone(), tv, Mult::Many);
        let r_tm = Tm::Proj(Rc::new(Tm::Var(0)), 1);
        let r_val = self.eval(cx, &r_tm);
        let r_ty_t = quote(&self.g, cx.lvl(), &comps[1]);
        cx.define(&rname, comps[1].clone(), r_val, mult);
        let x_tm = Tm::Proj(Rc::new(Tm::Var(1)), 0);
        let body = self.let_pattern(cx, pat, x_tm, comps[0].clone(), rest, result, expected, tail);
        cx.pop();
        cx.pop();
        Tm::Let(
            Rc::from(tname.as_str()),
            Mult::Many,
            Rc::new(tyt),
            Rc::new(t),
            Rc::new(Tm::Let(Rc::from(rname.as_str()), mult, Rc::new(r_ty_t), Rc::new(r_tm), Rc::new(body))),
        )
    }

    /// `let pat = t` (t already elaborated) followed by the rest of the block.
    #[allow(clippy::too_many_arguments)]
    fn let_pattern(
        &mut self,
        cx: &mut Cx,
        pat: &ast::Pattern,
        t: Tm,
        ty: Val,
        rest: &[Stmt],
        result: &Expr,
        expected: &Val,
        tail: bool,
    ) -> Tm {
        let name = match &pat.kind {
            ast::PatKind::Var(n) => n.clone(),
            ast::PatKind::Wild => "_".to_string(),
            _ => format!("$p{}", cx.lvl()),
        };
        if name == "_" && self.val_linear(&ty) {
            self.report_dropped(cx, &ty, pat.span);
        }
        let mult = self.named_mult(cx, &name, &ty, pat.span, Mult::Many);
        let v = self.eval(cx, &t);
        let tyt = quote(&self.g, cx.lvl(), &ty);
        cx.define(&name, ty, v, mult);
        let body = match &pat.kind {
            ast::PatKind::Var(_) | ast::PatKind::Wild => self.block_from(cx, rest, result, expected, tail),
            _ => {
                let scrut = mk(ExprKind::Var(name.clone()), pat.span);
                let arms = vec![(pat.clone(), None, ArmBody::Rest(rest, result))];
                self.elab_match(cx, &scrut, arms, Some(expected), tail, pat.span).0
            }
        };
        cx.pop();
        Tm::Let(Rc::from(name.as_str()), mult, Rc::new(tyt), Rc::new(t), Rc::new(body))
    }

    // ── concurrency forms (§8.5–8.6) ────────────────────────────────────────

    fn check_sched(&mut self, cx: &mut Cx, s: &Ident) -> Tm {
        let sched = self.ty_val(self.g.well_known.sched, vec![]);
        let e = mk(ExprKind::Var(s.name.clone()), s.span);
        self.check(cx, &e, &sched, false)
    }

    fn elab_when(&mut self, cx: &mut Cx, w: &ast::When) -> Tm {
        let saved = self.post_target.take();
        let t = self.elab_when_inner(cx, w);
        self.post_target = saved;
        t
    }

    fn elab_when_inner(&mut self, cx: &mut Cx, w: &ast::When) -> Tm {
        let st = self.check_sched(cx, &w.sched);
        let mut cowns = Vec::new();
        let mut tys = Vec::new();
        for (_, c) in &w.binds {
            let inner = self.fresh_meta_val(cx);
            let cown = self.ty_val(self.g.well_known.cown, vec![inner.clone()]);
            cowns.push(self.check(cx, c, &cown, false));
            tys.push(inner);
        }
        let start = cx.lvl();
        // The contents' refinements (a cown invariant, §8.5): facts on entry,
        // obligations on every value the body hands back.
        let many = tys.len() > 1;
        let invs: Vec<CownInv> = tys.iter().enumerate().filter_map(|(k, ty)| self.cown_inv(cx, ty, many.then_some(k))).collect();
        for ((n, _), ty) in w.binds.iter().zip(&tys) {
            let l = cx.bind(&n.name, ty.clone(), Mult::Many);
            if let Some(inv) = self.cown_inv(cx, ty, None) {
                let mut env = inv.args.clone();
                env.push(Val::var(l));
                for p in &inv.preds {
                    let f = self.inst_pred(p, env.clone());
                    cx.assume(f);
                }
            }
        }
        if !invs.is_empty() {
            self.post_target = Some(PostTarget { posts: Vec::new(), func: String::new(), binders: Vec::new(), invariants: invs });
        }
        // The body's type is in the outer context; shift by evaluating in the extended one.
        let expected = if tys.len() == 1 { tys[0].clone() } else { Val::TupleTy(tys.clone()) };
        let body = self.check_block(cx, &w.body, &expected, true);
        self.post_target = None;
        cx.truncate(start);
        let mut lam = body;
        for (n, _) in w.binds.iter().rev() {
            lam = Tm::Lam(Rc::from(n.name.as_str()), Mult::Many, Icit::Expl, Rc::new(lam));
        }
        Tm::PrimApp(Prim::When, vec![st, Tm::Tuple(cowns), lam])
    }

    pub fn elab_fork_join(&mut self, cx: &mut Cx, e: &Expr) -> (Tm, Val) {
        let saved = self.post_target.take();
        let r = self.elab_fork_join_inner(cx, e);
        self.post_target = saved;
        r
    }

    fn elab_fork_join_inner(&mut self, cx: &mut Cx, e: &Expr) -> (Tm, Val) {
        match &e.kind {
            ExprKind::Fork(s, body) => {
                let st = self.check_sched(cx, s);
                // The result type lives outside the behaviour, so its unknown is
                // created before the behaviour's binder.
                let rty = self.fresh_meta_val(cx);
                let start = cx.lvl();
                let unit = self.unit();
                cx.bind("_", unit, Mult::Many);
                let bt = self.check_block(cx, body, &rty, true);
                cx.truncate(start);
                let fut = self.ty_val(self.g.well_known.future, vec![rty]);
                (Tm::PrimApp(Prim::Fork, vec![st, Tm::Lam(Rc::from("_"), Mult::Many, Icit::Expl, Rc::new(bt))]), fut)
            }
            ExprKind::Join(binds, s, body) => {
                let st = self.check_sched(cx, s);
                let mut futs = Vec::new();
                let mut tys = Vec::new();
                for (_, f) in binds {
                    let inner = self.fresh_meta_val(cx);
                    let fut = self.ty_val(self.g.well_known.future, vec![inner.clone()]);
                    futs.push(self.check(cx, f, &fut, false));
                    tys.push(inner);
                }
                let rty = self.fresh_meta_val(cx);
                let start = cx.lvl();
                for ((n, _), ty) in binds.iter().zip(&tys) {
                    cx.bind(&n.name, ty.clone(), Mult::Many);
                }
                let bt = self.check_block(cx, body, &rty, true);
                cx.truncate(start);
                let mut lam = bt;
                for (n, _) in binds.iter().rev() {
                    lam = Tm::Lam(Rc::from(n.name.as_str()), Mult::Many, Icit::Expl, Rc::new(lam));
                }
                let fut = self.ty_val(self.g.well_known.future, vec![rty]);
                (Tm::PrimApp(Prim::Join, vec![st, Tm::Tuple(futs), lam]), fut)
            }
            _ => self.infer(cx, e),
        }
    }
}

fn pvar(n: &str, span: Span) -> ast::Pattern {
    ast::Pattern { kind: ast::PatKind::Var(n.to_string()), span }
}

/// Does `t`, a term over `total` binders (de Bruijn indices), mention a
/// binder at level `from` or later? `depth` counts binders inside `t`.
fn mentions_level_from(t: &Tm, total: usize, from: usize, depth: usize) -> bool {
    let rec = |x: &Tm, d: usize| mentions_level_from(x, total, from, d);
    match t {
        Tm::Var(i) => *i >= depth && total + depth - 1 - i >= from,
        Tm::App(f, a, ..) => rec(f, depth) || rec(a, depth),
        Tm::Lam(_, _, _, b) => rec(b, depth + 1),
        Tm::Pi(_, _, _, a, b) => rec(a, depth) || rec(b, depth + 1),
        Tm::Let(_, _, a, v, b) => rec(a, depth) || rec(v, depth) || rec(b, depth + 1),
        Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => v.iter().any(|x| rec(x, depth)),
        Tm::Proj(x, _) | Tm::Field(x, _, _) => rec(x, depth),
        Tm::Case(s, c) => {
            rec(s, depth)
                || c.branches.iter().any(|(_, n, b)| rec(b, depth + n))
                || c.lits.iter().any(|(_, b)| rec(b, depth))
                || c.default.as_ref().is_some_and(|b| rec(b, depth))
        }
        _ => false,
    }
}
