//! Expressions: bidirectional checking and inference.

use super::*;
use crate::syntax::ast::{Constraint, Expr, ExprKind, Ident, Stmt};
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
        // A use of a definition in compiled code: its implicit arguments
        // are checked against D125 (b) once the module's bodies are done.
        let inst = match (self.pending_inst.take(), &t) {
            (Some((d, span)), Tm::Def(d2)) if d == *d2 && self.in_spec == 0 && self.in_proof == 0 => Some((d, span)),
            _ => None,
        };
        let mut args = Vec::new();
        loop {
            match self.force(&ty) {
                Val::Pi(x, m, Icit::Impl, dom, c) => {
                    let mt = self.fresh_meta(cx);
                    self.name_meta(cx, &mt, &x, &dom, &t);
                    let mv = self.eval(cx, &mt);
                    // A dictionary (D136): found once its type is known.
                    let span = self.name_span;
                    let asked = self.inst_reqs.len();
                    self.note_dict(cx, &mv, &dom, span);
                    // A type's header's (#385).
                    let of_type = match t.head() {
                        Tm::TyCon(tid) => Some(*tid),
                        Tm::Con(c) => Some(self.g.cons[c.0 as usize].ty),
                        _ => None,
                    };
                    if let (true, Some(tid)) = (self.inst_reqs.len() > asked, of_type) {
                        if self.g.tys[tid.0 as usize].dicts > 0 {
                            self.inst_reqs[asked].of_type = Some(tid);
                            let r = self.inst_reqs[asked].clone();
                            if let Some(rs) = &mut self.type_dict_reqs {
                                rs.push(r);
                            }
                        }
                    }
                    args.push(mv.clone());
                    t = Tm::App(Rc::new(t), Rc::new(mt), Icit::Impl, m);
                    ty = apply_closure(&self.g, &c, mv);
                }
                _ => {
                    if let Some((callee, span)) = inst {
                        if !args.is_empty() {
                            self.insts.push(Inst { caller: self.cur_fn, callee, args, lvl: cx.lvl(), names: cx.names(), span });
                        }
                    }
                    return (t, ty);
                }
            }
        }
    }

    pub fn check(&mut self, cx: &mut Cx, e: &Expr, expected: &Val, tail: bool) -> Tm {
        let covered = std::mem::take(&mut self.alias_covered);
        // A value the function returns: its postconditions must hold of it (§7.1).
        let returned = tail
            && self.post_target.is_some()
            && !matches!(e.kind, ExprKind::If(..) | ExprKind::Match(..) | ExprKind::Block(..) | ExprKind::Try(_));
        // An `if`, `match` or block passes the expected type to each branch,
        // which meets any refinement in it; where refinements are not imposed
        // (an operator's operand, D71), the branches get the type without them.
        let compound = matches!(e.kind, ExprKind::If(..) | ExprKind::Match(..) | ExprKind::Block(..));
        let t = if covered && compound {
            let bare = self.force(expected);
            self.check_inner(cx, e, &bare, tail)
        } else {
            self.check_inner(cx, e, expected, tail)
        };
        let inferred = self.last_inferred.take();
        self.last_checked = inferred.clone();
        // A value checked against a refinement alias must satisfy it (D71),
        // unless the call it is passed to, or the function returning it,
        // already checks that alias, or its branches did.
        // A class's type with a base type (#360): only its own values.
        if !covered && !compound && !matches!(t, Tm::Error) {
            self.check_based(cx, expected, inferred.as_ref(), e.span);
        }
        if !covered && !returned && !compound && !matches!(t, Tm::Error) {
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
            self.oblige_posts_typed(cx, v, e.span, inferred.as_ref());
        }
        t
    }

    fn check_inner(&mut self, cx: &mut Cx, e: &Expr, expected: &Val, tail: bool) -> Tm {
        if matches!(&e.kind, ExprKind::Var(n) if Self::is_cursor(n)) {
            self.note_cursor(cx, Some(expected));
            return Tm::Error;
        }
        let exp = self.force(expected);
        // An instance's dictionary's field for a clause on one of its
        // class's types (#176): found as an implicit argument is.
        if matches!(&e.kind, ExprKind::Var(n) if n == super::classes::FIND_DICT) {
            let mt = self.fresh_meta(cx);
            let mv = self.eval(cx, &mt);
            self.note_dict(cx, &mv, &exp, e.span);
            return mt;
        }
        // A name where a type is expected is the type, not a record's
        // constructor of the same name (`String`, #170), applied too
        // (`Box b`): no constructor builds a type.
        if matches!(exp, Val::Univ(_)) && !cx.type_pos && {
            let mut h = e;
            while let ExprKind::App(f, _) = &h.kind {
                h = f;
            }
            matches!(h.kind, ExprKind::Con(_))
        } {
            cx.type_pos = true;
            let t = self.check_inner(cx, e, expected, tail);
            cx.type_pos = false;
            return t;
        }
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
                let nm = self.binder_name(&name, p.span);
                // Whether `own` here means anything is decided once the
                // parameter's type is known, by the usage check (D172 b).
                if *m == Mult::One {
                    self.lam_domains.insert(Rc::as_ptr(&nm) as *const u8 as usize, ((**a).clone(), cx.lvl()));
                }
                // A domain with an inline refinement (`(x~a, contains xs x)`,
                // `(i~Nat, i < n)`): the parameter has its base type and the
                // predicates as facts, so a type inferred from it (`map (\x
                // -> x) xs`) doesn't gain the refinement.
                let anon = match self.refined_alias(a) {
                    Some((d, args)) if self.is_direct_alias(a) && is_anon_alias(&self.g, d) => {
                        unfold(&self.g, a).map(|base| (base, self.alias_preds.get(&d).cloned().unwrap_or_default(), args))
                    }
                    _ => None,
                };
                let pty = anon.as_ref().map_or_else(|| (**a).clone(), |(base, _, _)| base.clone());
                let l = cx.bind(&name, pty, *m);
                if let Some((_, preds, args)) = anon {
                    for p in &preds {
                        let mut env = args.clone();
                        env.push(Val::var(l));
                        let f = self.inst_pred(p, env);
                        cx.assume(f);
                    }
                }
                cx.locals[l].sub = map_sub.map(|e| e.p);
                cx.locals[l].sub_cond = map_sub.and_then(|e| e.cond);
                if simple && name != "_" {
                    self.bound_at(cx, l, p.span);
                }
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
                    self.elab_match(cx, &scrut, arm, Some(&body_ty), true, p.span).0
                };
                self.post_target = saved_post;
                cx.pop();
                Tm::Lam(nm, *m, Icit::Expl, Rc::new(t))
            }
            (ExprKind::If(c, t, f), _) => {
                let b = self.bool_ty();
                let ct = self.check(cx, c, &b, false);
                let cv = self.eval(cx, &ct);
                let saved = cx.facts.len();
                cx.assume(self.is_bool(cv.clone(), true));
                self.probe(cx, c.span, ProbeKind::Then, t.span, saved);
                let tt = self.check(cx, t, expected, tail);
                cx.facts.truncate(saved);
                cx.assume(self.is_bool(cv, false));
                self.probe(cx, c.span, ProbeKind::Else, f.span, saved);
                let ft = self.check(cx, f, expected, tail);
                cx.facts.truncate(saved);
                self.if_tm(ct, tt, ft)
            }
            (ExprKind::Match(s, arms), _) => {
                let arms_in = arms.iter().map(|a| (a.pat.clone(), a.guard.as_ref(), ArmBody::Expr(&a.body))).collect();
                self.elab_match(cx, s, arms_in, Some(expected), tail, e.span).0
            }
            (ExprKind::Block(b), _) => self.check_block(cx, b, expected, tail),
            (ExprKind::Try(x), _) => {
                if !tail {
                    self.try_not_tail(e.span);
                }
                self.check(cx, x, &exp, tail)
            }
            (ExprKind::Lit(ast::Lit::Int(s)), Val::TyCon(id, _))
                if Some(*id) == self.g.well_known.int =>
            {
                Tm::Lit(Lit::int(self.number(s)))
            }
            (ExprKind::Lit(ast::Lit::Int(_)), Val::TyCon(..) | Val::TupleTy(_) | Val::Pi(..)) => {
                let shown = self.show_val(cx, &exp);
                self.err(
                    Diagnostic::error("E0201", format!("type mismatch: expected `{shown}`, found a number"), e.span)
                        .with_label(format!("this is a number, not a `{shown}`")),
                );
                Tm::Error
            }
            // `+ - *` of a type with an instance of the operator's class (M24).
            (ExprKind::Binary(op @ (Op::Add | Op::Sub | Op::Mul), l, r), Val::TyCon(..))
                if Self::class_op(*op).is_some_and(|(c, m, _, _)| self.operator_method(cx, c, m, &exp).is_some()) =>
            {
                let lt = self.check(cx, l, expected, false);
                match self.class_operator(cx, *op, lt, expected, r, e.span) {
                    Ok((t, ty)) => {
                        self.last_inferred = Some(ty);
                        t
                    }
                    Err(_) => Tm::Error,
                }
            }
            (ExprKind::Binary(op, l, r), Val::TyCon(..))
                if matches!(op, Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Rem | Op::Concat) =>
            {
                // The result has the operands' type, so check both against it
                // (as written: a mismatch names `Small`, not `Nat`).
                let (lt, lown) = self.check_operand(cx, l, expected);
                let (rt, rown) = self.check_operand(cx, r, expected);
                self.operand_types = Some((lown.unwrap_or_else(|| expected.clone()), rown.unwrap_or_else(|| expected.clone())));
                self.finish_arith(cx, *op, lt, rt, expected.clone(), l.span.to(r.span), e.span).0
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
                let ts = items.iter().zip(tys.iter().cloned()).map(|(it, t)| self.check(cx, it, &t, false)).collect();
                Tm::Tuple(ts)
            }
            (ExprKind::Tuple(items), Val::Univ(_)) => {
                Tm::TupleTy(items.iter().map(|it| self.elab_type(cx, it)).collect())
            }
            (ExprKind::Unit, Val::Univ(_)) => Tm::TupleTy(vec![]),
            (ExprKind::Template(..), _) => self.elab_template(cx, e, Some(expected)).0,
            _ => {
                // A dictionary (D136): its class's type constructor (M25) comes
                // from the instance's head before its functions are checked.
                let dict = {
                    let mut h = e;
                    while let ExprKind::App(f, _) = &h.kind {
                        h = f;
                    }
                    matches!(&h.kind, ExprKind::Con(n) if n.starts_with("$mk#")) && !std::ptr::eq(h, e)
                };
                // A function type whose parameter is refined in place (`(x~a ->
                // b, contains xs x)`), with the parameter's base type: the
                // value's own types (a `let`-bound lambda's parameter, a
                // partial application's) are solved to it, so the value
                // doesn't take on the precondition; the refinements are
                // compared below.
                let unrefined = match self.force(expected) {
                    Val::Pi(x, m, i, dom, c) if self.is_direct_alias(&dom) && self.refined_alias(&dom).is_some_and(|(d, _)| is_anon_alias(&self.g, d)) => {
                        unfold(&self.g, &dom).map(|base| Val::Pi(x, m, i, Rc::new(base), c))
                    }
                    _ => None,
                };
                if matches!(e.kind, ExprKind::App(..)) && (dict || self.has_refined(cx, expected, 0) || matches!(self.force(expected), Val::Univ(_))) {
                    self.app_expected = Some(unrefined.clone().unwrap_or_else(|| expected.clone()));
                }
                let (t, ty) = self.infer(cx, e);
                self.app_expected = None;
                // A branch of an `if` or `match` whose type is inferred
                // (D135): its range joins the others'; the branches share
                // only their base type.
                let shared = match self.join_of(expected) {
                    Some(m) => {
                        let r = self.type_range(&ty);
                        self.join_branch(m, r);
                        if r.is_some() { self.arith_base(&ty) } else { ty.clone() }
                    }
                    None => ty.clone(),
                };
                if let Some(u) = &unrefined {
                    let _ = unify(&self.g, cx.lvl(), u, &shared);
                }
                if !self.unify_at(cx, expected, &shared, e.span, "this expression") {
                    return Tm::Error;
                }
                // A refinement inside a type argument is never gained (D71).
                // An instance's function with a signature of its own, in its
                // dictionary, is checked to refine the class's by the prover
                // (#225, E0371).
                if self.refined_in_dict(t.head()) {
                    self.last_inferred = Some(ty);
                    return t;
                }
                // A class's function as a value: at a known instance whose
                // function has a signature of its own, it has that
                // signature (#252), compared with the type expected here.
                // Through a refinement alias, that comparison is the check
                // that it gives the alias's values.
                let ty = match self.class_use(cx, &t) {
                    Some((m, f, term, false)) => {
                        if !self.inst_reqs.is_empty() {
                            self.solve_instances(false);
                            self.retry_waiting(false);
                        }
                        match self.instance_value(cx, &term) {
                            Some((direct, dty)) => {
                                self.class_value_uses.push((m, f, e.span, true));
                                self.spec_fn_type(cx, &direct, dty)
                            }
                            None => ty,
                        }
                    }
                    _ => ty,
                };
                let mut gained = self.refined_mismatch(cx, expected, &ty, e.span);
                // A class's type at an instance not found yet (`Seq.Elem` of
                // `Seq.uncons xs`, #190): find the instances the types known
                // so far choose, and look again.
                if gained.is_some() && !self.inst_reqs.is_empty() {
                    self.solve_instances(false);
                    self.retry_waiting(false);
                    gained = self.refined_mismatch(cx, expected, &ty, e.span);
                }
                if let Some(g) = gained {
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
            ExprKind::When(w) => {
                let t = self.elab_when(cx, w);
                (t, self.unit())
            }
            ExprKind::Forall(..) => self.elab_forall(cx, e),
            ExprKind::Var(n) => {
                let (t, ty) = self.infer_var(cx, n, e.span);
                if self.in_app_head {
                    return (t, ty);
                }
                // A local defined as a class's function, used as a value
                // (#252).
                if let (Tm::Var(_), Some((m, f, _, false))) = (&t, self.class_use(cx, &t)) {
                    self.class_value_uses.push((m, f, e.span, false));
                }
                // A function with a specification, as a value (D85).
                let ty = self.refined_fn_type(cx, &t, ty);
                (t, ty)
            }
            ExprKind::Con(n) => match self.resolve(n, cx.type_pos) {
                Some(Sym::Ty(t)) if !cx.type_pos && self.class_defs.contains_key(&t) => {
                    let name = self.class_defs[&t].name.clone();
                    self.err(
                        Diagnostic::error("E0287", format!("a dictionary of class `{name}` is built only by an instance"), e.span)
                            .with_help(format!("declare `instance {name} …`; its functions' bodies and lemmas' proofs are checked there")),
                    );
                    (Tm::Error, Val::Error)
                }
                Some(s) => {
                    if let Sym::Con(c) = s {
                        self.check_dict_con(c, e.span);
                    }
                    self.name_span = e.span;
                    self.index_sym(e.span, s);
                    let (t, ty) = self.sym_term(cx, s, e.span);
                    self.insert(cx, t, ty)
                }
                None => {
                    let mut d = Diagnostic::error("E0204", format!("unknown name `{n}`"), e.span).with_label("not found");
                    if let Some(m) = self.private_in_imports(n) {
                        d = self.private_help(d, &self.cur, &m, n);
                    }
                    self.err(d);
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
                    (Tm::Tuple(ts), Val::TupleTy(tys.into()))
                }
            }
            ExprKind::List(items) => {
                // The elements decide the element type together: each is
                // checked against an unknown of its own, and the element type
                // is their join, whatever their order.
                let elem = self.fresh_meta_val(cx);
                let joined: Vec<MetaId> = match &elem {
                    Val::Neutral(Head::Meta(m), _) => vec![*m],
                    _ => Vec::new(),
                };
                let mut ts = Vec::new();
                let mut joins = Vec::new();
                for it in items {
                    let (own, metas) = self.own_unknowns(cx, &elem, &joined);
                    let t = self.check(cx, it, &own, false);
                    joins.push(JoinArg { span: it.span, dom: elem.clone(), own, tm: t.clone(), metas });
                    ts.push(t);
                }
                self.join_args(cx, &joined, joins);
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
                    let n = self.number(s);
                    return (Tm::Lit(Lit::int(-n)), int);
                }
                let (t, xty) = self.infer(cx, x);
                self.find_type_dicts(&xty);
                // `-x` on a type with an instance of `Neg` (M24).
                if let Some(m) = self.operator_method(cx, "Neg", "neg", &xty) {
                    let (f, fty) = self.sym_term(cx, Sym::Def(m), e.span);
                    self.name_span = e.span;
                    let (f, fty) = self.insert(cx, f, fty);
                    return self.apply_tm(cx, f, fty, t, &xty, x.span);
                }
                if !self.unify_at(cx, &int, &xty, x.span, "this expression") {
                    return (Tm::Error, int);
                }
                // The operand's bounds, negated (D135).
                let ty = match self.type_range(&xty) {
                    Some(r) if r.lo.is_some() || r.hi.is_some() => {
                        let neg = |b: Option<i128>| b.and_then(|b| b.checked_neg());
                        self.range_type(super::interval::Range { lo: neg(r.hi), hi: neg(r.lo) })
                    }
                    _ => int,
                };
                (Tm::PrimApp(Prim::Neg, vec![t]), ty)
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
                // An element of an array (D133): of its element type, which
                // the prover is also given (its refinement holds of it).
                let elem = self.fresh_meta_val(cx);
                let arr = self.array_of(elem.clone());
                let nat = self.nat();
                let at = self.check(cx, a, &arr, false);
                // Indexing uses the whole array: at runtime, it may not drop
                // the other elements when they are resources (D156, E0407).
                if self.in_spec == 0 && self.in_proof == 0 && self.val_linear(&elem) {
                    self.part_reported_at(cx, &at);
                    let shown = self.show_val(cx, &elem);
                    self.err(
                        Diagnostic::error("E0407", format!("indexing would drop the array's other elements, and each is a resource (`{shown}`)"), e.span)
                            .with_label("indexing uses the whole array")
                            .with_help("keep the resources in a `List` and take it apart with `match`, using each one"),
                    );
                }
                let it = self.check(cx, i, &nat, false);
                let (av, iv) = (self.eval(cx, &at), self.eval(cx, &it));
                let goal = Self::prim_val(Prim::Lt, vec![iv, Self::prim_val(Prim::Len, vec![av])]);
                let text = format!("{} < len {}", self.src_text(i.span), self.src_text(a.span));
                self.oblige(cx, e.span, ObKind::Index, text, goal, None);
                let et = quote(&self.g, cx.lvl(), &elem);
                (Tm::PrimApp(Prim::Index, vec![at, it, et]), elem)
            }
            ExprKind::Lambda(pats, body) => {
                // Infer a lambda: parameter types are unknowns.
                let mut binders = Vec::new();
                let start = cx.lvl();
                // A parameter that is a pattern (`\(a, b) -> …`) is a
                // variable of its own, taken apart by a `match` around the
                // body, as in checking mode.
                let mut body: Expr = (**body).clone();
                let mut taken_apart = Vec::new();
                // Each parameter's type is an unknown of the lambda's
                // context, not of the parameters before it: applied to a
                // value that isn't a variable (`(\a b -> …) 1 "two"`), a
                // type depending on `a` couldn't be solved.
                let tys: Vec<Val> = pats.iter().map(|_| self.fresh_meta_val(cx)).collect();
                for (p, a) in pats.iter().zip(tys) {
                    let name = match &p.kind {
                        ast::PatKind::Var(n) => n.clone(),
                        ast::PatKind::Wild => "_".to_string(),
                        _ => {
                            let n = format!("$arg{}", cx.lvl());
                            taken_apart.push((n.clone(), p.clone()));
                            n
                        }
                    };
                    let at = quote(&self.g, cx.lvl(), &a);
                    let l = cx.bind(&name, a, Mult::Many);
                    if name != "_" {
                        self.bound_at(cx, l, p.span);
                    }
                    binders.push((Rc::<str>::from(name.as_str()), at));
                }
                for (n, p) in taken_apart.into_iter().rev() {
                    // At the pattern's place, so a case it leaves out is
                    // reported about the pattern.
                    let span = p.span;
                    let scrut = mk(ExprKind::Var(n), p.span);
                    let arm = ast::Arm { pat: p, guard: None, body, span };
                    body = mk(ExprKind::Match(Box::new(scrut), vec![arm]), span);
                }
                // A lambda's results are not the function's.
                let saved_post = self.post_target.take();
                let (bt, bty) = self.infer(cx, &body);
                let bty = crate::core::strengthen(&self.g, &bty, start);
                self.post_target = saved_post;
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
                // Numbers from the branches: the hull of their ranges (D135).
                let m = match &mv {
                    Val::Neutral(Head::Meta(m), _) => Some(*m),
                    _ => None,
                };
                if let Some(m) = m {
                    self.joins.insert(m, super::interval::Join::Empty);
                }
                let t = self.check(cx, e, &mv, false);
                match m.and_then(|m| self.joins.remove(&m)) {
                    Some(super::interval::Join::Range(r)) => {
                        let ty = self.range_type(r);
                        (t, ty)
                    }
                    _ => (t, mv),
                }
            }
            ExprKind::Par(items) => {
                let tuple = mk(ExprKind::Tuple(items.clone()), e.span);
                let (t, ty) = self.infer(cx, &tuple);
                (Tm::PrimApp(Prim::Par, vec![t]), ty)
            }
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
            ExprKind::Template(..) => self.elab_template(cx, e, None),
            ExprKind::Error => (Tm::Error, Val::Error),
        }
    }

    // ── names ───────────────────────────────────────────────────────────────

    fn infer_var(&mut self, cx: &mut Cx, n: &str, span: Span) -> (Tm, Val) {
        if Self::is_cursor(n) {
            self.note_cursor(cx, None);
            return (Tm::Error, Val::Error);
        }
        if let Some(l) = cx.lookup(n) {
            self.index_local(cx, l, span);
            let ty = cx.ty_of(l);
            if self.map_elem_sub.is_some() {
                self.map_elem_sub = None;
            }
            // A use of a parameter, for the promises its body makes (#102):
            // code in a specification or proof never runs.
            let ctx = self.use_ctx.take();
            if let (Mult::Zero, Some(f)) = (cx.locals[l].mult, self.cur_fn) {
                if !cx.type_pos && self.in_spec == 0 && self.in_proof == 0 && self.in_erased == 0 {
                    self.ghost_uses.entry((f, cx.locals[l].name.to_string())).or_default().push(span);
                }
            }
            if let (Some(k), Some(f)) = (cx.locals[l].param, self.cur_fn) {
                if self.in_spec == 0 && self.in_proof == 0 {
                    self.param_uses.entry((f, k)).or_default().push(ctx.unwrap_or_default());
                }
            }
            return (cx.var(l), ty);
        }
        if n == "__class_lemma" {
            // A class's lemma: assumed, each instance proving it (D136).
            if self.proof_goal.is_some() && self.cur_fn.is_some_and(|d| self.class_lemmas.contains(&d)) {
                return (Tm::Tuple(vec![]), self.unit());
            }
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
                self.name_span = span;
                if let Sym::Con(c) = s {
                    self.check_dict_con(c, span);
                }
                if let Sym::Ty(t) = s {
                    if !cx.type_pos && self.class_defs.contains_key(&t) {
                        let name = self.class_defs[&t].name.clone();
                        self.err(
                            Diagnostic::error("E0287", format!("a dictionary of class `{name}` is built only by an instance"), span)
                                .with_help(format!("declare `instance {name} …`; its functions' bodies and lemmas' proofs are checked there")),
                        );
                        return (Tm::Error, Val::Error);
                    }
                }
                if !Self::is_template_call(n) {
                    self.index_sym(span, s);
                }
                if let Sym::Def(d) = s {
                    self.note_reference(d, span);
                    if !self.in_app_head && !self.g.defs[d.0 as usize].comptime.is_empty() {
                        self.err(
                            Diagnostic::error("E0271", format!("`{n}` is a compile-time function, so it must be called with all its arguments"), span)
                                .with_help("it is expanded where it is called; wrap the call in a lambda to pass it as a value, e.g. `\\x -> f 2 x`"),
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
                    let mut d = Diagnostic::error("E0204", format!("unknown name `{n}`"), span).with_label("not found");
                    if let Some(m) = self.private_in_imports(n) {
                        d = self.private_help(d, &self.cur, &m, n);
                    } else if let Some(h) = self.std_export_help(n) {
                        d = d.with_help(h);
                    }
                    self.err(d);
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
        let (args, conds) = match self.map_elem_sub.take() {
            Some(e) => (vec![Some(e.p)], e.cond.map(|c| (0, c)).into_iter().collect()),
            None => (vec![], vec![]),
        };
        self.calls.push(CallRec { caller, callee: d, args, same: Vec::new(), span, conds });
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
                self.pending_inst = Some((d, span));
                (Tm::Def(d), eval(&self.g, &empty, &ty))
            }
            Sym::Ty(t) => {
                let ti = &self.g.tys[t.0 as usize];
                // Its header's dictionaries (#385) are implicit, found where
                // it is written.
                let first_dict = ti.params.len() - ti.dicts;
                let params = ti.params.clone();
                let ty = Elab::pi_of(
                    &params
                        .iter()
                        .enumerate()
                        .map(|(k, (n, ty))| (n.clone(), Mult::Many, if k < first_dict { Icit::Expl } else { Icit::Impl }, ty.clone()))
                        .collect::<Vec<_>>(),
                    Tm::Univ(0),
                );
                (Tm::TyCon(t), eval(&self.g, &empty, &ty))
            }
            Sym::Con(c) => {
                let ty = self.con_type(c);
                (Tm::Con(c), eval(&self.g, &empty, &ty))
            }
            Sym::Univ => (Tm::Univ(0), Val::Univ(1)),
            Sym::Len => {
                self.err(Diagnostic::error(
                    "E0214",
                    "`len` must be applied to an argument here, e.g. `len x`".to_string(),
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
                let n = self.number(s);
                let mv = self.fresh_meta_val(cx);
                self.deferred.push(Deferred {
                    givens: self.givens.clone(),
                    ty: mv.clone(),
                    kind: OpClass::Numeric,
                    span,
                    what: "a number literal".into(),
                    lvl: cx.lvl(),
                    names: cx.names(),
                    owner: self.cur_fn,
                });
                (Tm::Lit(Lit::int(n)), mv)
            }
            ast::Lit::Byte(b) => (Tm::Lit(Lit::Num(*b as i128)), self.u8_ty()),
            ast::Lit::Char(c) => (Tm::Lit(Lit::Num(*c as i128)), self.char_ty()),
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

    pub fn bool_lit(&self, b: bool) -> Tm {
        let c = if b { self.g.well_known.true_con } else { self.g.well_known.false_con };
        c.map(|c| Tm::ConApp(c, vec![])).unwrap_or(Tm::Error)
    }

    // ── application ─────────────────────────────────────────────────────────

    /// `C.Name t` (#133): the class's type `Name` at `t`, read from the
    /// dictionary found for `t` once `t` is known; `C.Name s h` for a class
    /// of several parameters (#145), one type for each.
    #[allow(clippy::too_many_arguments)]
    fn elab_assoc(&mut self, cx: &mut Cx, tid: TyId, acc: DefId, class_span: Span, name: &ast::Ident, args: &[&Expr], span: Span) -> (Tm, Val) {
        self.index_sym(class_span, Sym::Ty(tid));
        self.index_sym(name.span, Sym::Def(acc));
        self.note_reference(acc, span);
        let (mut t, mut ty) = self.sym_term(cx, Sym::Def(acc), span);
        for arg in args {
            let Val::Pi(_, m, _, dom, c) = self.force(&ty) else { return (Tm::Error, Val::Error) };
            let saved = cx.type_pos;
            cx.type_pos = true;
            self.in_spec += 1;
            let at = self.check(cx, arg, &dom, false);
            self.in_spec -= 1;
            cx.type_pos = saved;
            let av = self.eval(cx, &at);
            t = Tm::App(Rc::new(t), Rc::new(at), Icit::Expl, m);
            ty = apply_closure(&self.g, &c, av);
        }
        self.name_span = span;
        let n = self.inst_reqs.len();
        let r = self.insert(cx, t, ty);
        let shown = self.g.defs[acc.0 as usize].name.to_string();
        for q in &mut self.inst_reqs[n..] {
            q.assoc = Some(shown.clone());
        }
        r
    }

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

        // A class's type at a type, `Display.Options Money` (#133).
        if let ExprKind::Field(x, name) = &head.kind {
            if let ExprKind::Con(c) = &x.kind {
                if let Some(Sym::Ty(tid)) = self.resolve(c, true) {
                    if let Some(acc) = self.assoc_defs.get(&(tid, name.name.clone())).copied() {
                        // One type for each of the class's parameters (#145).
                        let n = self.class_defs.get(&tid).map_or(1, |c| c.params.len());
                        if args.len() < n {
                            return self.assoc_without_types(tid, acc, x.span, name, e.span);
                        }
                        let r = self.elab_assoc(cx, tid, acc, x.span, name, &args[..n], head.span.to(args[n - 1].span));
                        return self.apply_rest(cx, r, &args[n..], e.span);
                    }
                }
            }
        }

        // Overloaded built-ins (D38).
        if let ExprKind::Var(n) = &head.kind {
            if cx.lookup(n).is_none() {
                if let Some(Sym::Len) = self.resolve(n, false) {
                    let (at, aty) = self.infer(cx, args[0]);
                    self.deferred.push(Deferred {
                        givens: self.givens.clone(),
                        ty: aty,
                        kind: OpClass::HasLen,
                        span: args[0].span,
                        what: "`len`".into(),
                        lvl: cx.lvl(),
                        names: cx.names(),
                        owner: self.cur_fn,
                    });
                    let r = (Tm::PrimApp(Prim::Len, vec![at]), self.nat());
                    return self.apply_rest(cx, r, &args[1..], e.span);
                }
            }
        }

        // A function value passed here is applied to an element of a list
        // that is part of a parameter (#102): its call is recorded with that
        // argument (`list.map (f k) xs`, the parameter after `k`).
        let elem_sub = self.map_elem_sub.take();
        let ncalls = self.calls.len();
        let saved_head = std::mem::replace(&mut self.in_app_head, true);
        // A parameter called here (#102): what its first argument is part of.
        if let ExprKind::Var(n) = &head.kind {
            if cx.lookup(n).is_some_and(|l| cx.locals[l].param.is_some()) {
                self.use_ctx = Some(args.first().and_then(|a| self.part_of(cx, a)).map(|(j, c)| vec![(j, c)]).unwrap_or_default());
            }
        }
        let meta_start = self.g.metas.borrow().len();
        let (ft, fty) = self.infer(cx, head);
        // Where an implicit argument after an explicit one (#161) is shown.
        let head_name_span = self.name_span;
        self.use_ctx = None;
        self.in_app_head = saved_head;
        self.note_tag_call(head, &fty, e.span, args[0]);
        // `debug x` shows each of `x`'s fields: they are read (#126).
        if let (ExprKind::Var(n), Some(d)) = (&head.kind, self.std_def("debug")) {
            if cx.lookup(n).is_none() && self.resolve(n, false) == Some(Sym::Def(d)) {
                if let Val::Pi(_, _, _, dom, _) = self.force(&fty) {
                    self.observe(args[0].span, (*dom).clone());
                }
            }
        }
        let head_call = (self.calls.len() == ncalls + 1 && matches!(head.kind, ExprKind::Var(_))).then_some(ncalls);
        if let Some(i) = head_call {
            let mut conds = Vec::new();
            let mut classified = Vec::new();
            let mut same = Vec::new();
            for (k, a) in args.iter().enumerate() {
                let part = self.part_of(cx, a);
                if let Some((_, Some(c))) = part {
                    conds.push((k, c));
                }
                classified.push(part.map(|(p, _)| p));
                same.push(self.param_itself(cx, a));
            }
            if let Some(e) = elem_sub {
                let callee = self.calls[i].callee;
                if self.fn_meta.get(&callee).is_some_and(|m| m.params.len() > args.len()) {
                    if let Some(c) = e.cond {
                        conds.push((classified.len(), c));
                    }
                    classified.push(Some(e.p));
                }
            }
            self.calls[i].args = classified;
            self.calls[i].same = same;
            self.calls[i].conds = conds;
        }
        // What the callee's signature says about its function parameters
        // (#102): refinements over later parameters, and promises to call
        // them only with elements of a list.
        // A generic function's name comes with its implicit arguments.
        let callee_spec = crate::core::head_def(&ft).and_then(|d| self.specs.get(&d));
        let callee_def = crate::core::head_def(&ft);
        let late = callee_spec.map(|s| s.late.clone()).unwrap_or_default();
        let late: Vec<Late> = late.into_iter().map(|l| Late { deps: self.late_deps(&l), ..l }).collect();
        let n_implicit = callee_spec.map_or(0, |s| s.n_implicit);
        let inner = callee_spec.map(|s| s.inner.clone()).unwrap_or_default();
        self.head_checks_aliases = match &ft {
            Tm::Def(d) => self.specs.get(d).is_some_and(|s| s.preds.iter().any(|p| p.alias.is_some() && !p.is_post)),
            Tm::Con(c) => self.con_invs.contains_key(c),
            _ => false,
        };
        let wants_type = matches!(want.as_ref().map(|w| self.force(w)), Some(Val::Univ(_)));
        let (ft, fty) = match want {
            Some(w) => self.presolve_result(cx, ft, fty, args.len(), &w),
            None => (ft, fty),
        };
        let head_text = self.src_text(head.span);
        let mut ready: HashMap<usize, (Tm, Val)> = HashMap::new();
        let saved_arg_of = self.arg_of.replace(head_text);
        let (ft, fty) = self.look_ahead(cx, ft, fty, &args, head_name_span, &mut ready);
        self.arg_of = saved_arg_of;
        // `Tx a`, where `Tx` names an abstract type of another module whose
        // constructor shares its name (D155).
        if let Tm::TyCon(tid) = &ft {
            let tid = *tid;
            // Where a `Type` is expected (a type function's result), it is the type.
            if self.sealed_from(tid).is_some() && !cx.type_pos && !wants_type {
                self.err(self.sealed_error(tid, "constructors", head.span));
                for a in &args {
                    let _ = self.infer(cx, a);
                }
                return (Tm::Error, Val::Error);
            }
        }
        // Type parameters several arguments decide together.
        let joined = self.joined_params(cx, &fty, &args, &ready, meta_start);
        let mut joins = Vec::new();
        let mut t = ft;
        let mut ty = fty;
        let head_text = self.src_text(head.span);
        let saved_arg_of = self.arg_of.replace(head_text);
        for (k, a) in args.iter().enumerate() {
            let mut expected = None;
            if let Some(l) = late.iter().find(|l| l.binder == super::expl_binder(n_implicit, &inner, k)) {
                if !ready.contains_key(&k) && l.deps.iter().all(|j| super::expl_index(n_implicit, &inner, *j).is_some_and(|j| j < args.len())) {
                    let (t1, ty1, e) = self.late_expected(cx, t, ty, k, l, &late, &args, &mut ready);
                    (t, ty, expected) = (t1, ty1, e);
                }
            }
            let elem = callee_def.and_then(|d| self.elem_sub(cx, d, k, &args));
            // A parameter passed here (#102): it is called only with parts
            // of what the callee promises its function `k` gets.
            if let (ExprKind::Var(n), Some(d)) = (&a.kind, callee_def) {
                if cx.lookup(n).is_some_and(|l| cx.locals[l].param.is_some()) {
                    let mut ctx = Vec::new();
                    for (j, aj) in args.iter().enumerate() {
                        if j == k {
                            continue;
                        }
                        if let Some(p) = self.part_or_param(cx, aj) {
                            let c = self.new_elem_cond(vec![(d, k, j)]);
                            ctx.push((p, Some(c)));
                        }
                    }
                    self.use_ctx = Some(ctx);
                }
            }
            // An argument deciding a type parameter with others: checked
            // against its own unknown for it, joined with theirs below.
            let mut join = None;
            if !joined.is_empty() && !ready.contains_key(&k) {
                (t, ty) = self.insert(cx, t, ty);
                if let Val::Pi(_, _, Icit::Expl, dom, _) = self.force(&ty) {
                    let dom = expected.clone().unwrap_or((*dom).clone());
                    let (own, metas) = self.own_unknowns(cx, &dom, &joined);
                    if !metas.is_empty() {
                        expected = Some(own.clone());
                        join = Some((dom, own, metas));
                    }
                }
            }
            self.name_span = head_name_span;
            let (t2, ty2) = self.apply_one_as(cx, t, ty, a, expected, elem, ready.remove(&k));
            if let (Some((dom, own, metas)), Tm::App(_, at, Icit::Expl, _)) = (join, &t2) {
                joins.push(JoinArg { span: a.span, dom, own, tm: (**at).clone(), metas });
            }
            self.use_ctx = None;
            self.map_elem_sub = None;
            t = t2;
            ty = ty2;
        }
        self.join_args(cx, &joined, joins);
        self.arg_of = saved_arg_of;
        self.name_span = head_name_span;
        let (t, ty) = self.insert(cx, t, ty);
        // A call at a known instance whose function has a signature of its
        // own has that function's result type (#289).
        let (ty, typed) = match self.instance_call_type(cx, &t) {
            Some(ity) => (ity, true),
            None => (ty, false),
        };
        self.call_obligations(cx, &t, e.span, head.span, typed);
        // A partial application (D86).
        let ty = self.refined_fn_type(cx, &t, ty);
        // A compile-time argument that isn't known: its type may not compute
        // either, so don't also report a mismatch.
        if !self.check_comptime_call(cx, &t, &args, e.span) {
            return (Tm::Error, Val::Error);
        }
        // A call with effects is a value of its own (§7.1).
        let t = self.mark_effects(cx, t, &ty);
        (t, ty)
    }

    /// The type parameters of this call (unknowns made since `start`) that
    /// two or more of its arguments decide: those whose parameters' types
    /// mention them outside a function type. One that a function type
    /// mentions is left to be decided in order, as before.
    fn joined_params(&self, cx: &Cx, ty: &Val, args: &[&Expr], ready: &HashMap<usize, (Tm, Val)>, start: usize) -> Vec<MetaId> {
        let mut count: Vec<(MetaId, usize)> = Vec::new();
        let mut in_fn: Vec<MetaId> = Vec::new();
        let mut r = ty.clone();
        for k in 0..args.len() {
            let Val::Pi(_, _, Icit::Expl, dom, c) = self.force(&r) else { break };
            let q = quote(&self.g, cx.lvl() + k, &dom);
            let mut ms = Vec::new();
            metas_in(&q, &mut ms);
            ms.retain(|m| {
                m.0 as usize >= start
                    && self.g.meta(*m).is_none()
                    && self.g.meta_origins.borrow().get(m).is_some_and(|o| o.is_type && o.arity == 0)
            });
            if has_pi(&q) {
                in_fn.extend(ms);
            } else if !ready.contains_key(&k) {
                for m in ms {
                    match count.iter_mut().find(|(x, _)| *x == m) {
                        Some((_, n)) => *n += 1,
                        None => count.push((m, 1)),
                    }
                }
            }
            r = apply_closure(&self.g, &c, Val::var(cx.lvl() + k));
        }
        count.into_iter().filter(|(m, n)| *n >= 2 && !in_fn.contains(m)).map(|(m, _)| m).collect()
    }

    /// `dom` with each of the unknowns `joined` it mentions, still unsolved,
    /// replaced by a fresh one: the type a value deciding them with others
    /// is checked against, and the pairs replaced.
    pub fn own_unknowns(&mut self, cx: &Cx, dom: &Val, joined: &[MetaId]) -> (Val, Vec<(MetaId, MetaId)>) {
        let mut q = quote(&self.g, cx.lvl(), dom);
        let mut pairs = Vec::new();
        for &m in joined {
            if self.g.meta(m).is_some() || meta_app(&q, m).is_none() {
                continue;
            }
            let fresh = self.g.fresh_meta();
            let origin = self.g.meta_origins.borrow().get(&m).cloned();
            if let Some(o) = origin {
                self.g.meta_origins.borrow_mut().insert(fresh, o);
            }
            q = rename_meta(&q, m, fresh);
            pairs.push((m, fresh));
        }
        if pairs.is_empty() {
            return (dom.clone(), pairs);
        }
        (self.eval(cx, &q), pairs)
    }

    /// Decide the type parameters `joined` from the values checked against
    /// their own unknowns for them (`own_unknowns`): each is the join of
    /// what the values gave it (numbers' ranges joined, D135), so no value
    /// decides it before the others. Each value is then checked against its
    /// parameter's type, as it would have been against it directly.
    pub fn join_args(&mut self, cx: &Cx, joined: &[MetaId], args: Vec<JoinArg>) {
        if args.is_empty() {
            return;
        }
        for &m in joined {
            if self.g.meta(m).is_some() {
                continue;
            }
            let mut found: Option<Val> = None;
            let mut constants = Vec::new();
            let mut target = None;
            for a in &args {
                let Some(&(_, own)) = a.metas.iter().find(|(x, _)| *x == m) else { continue };
                let q = quote(&self.g, cx.lvl(), &a.dom);
                let Some(app) = meta_app(&q, m) else { continue };
                let v = self.eval(cx, &rename_meta(&app, m, own));
                if target.is_none() {
                    target = Some(self.eval(cx, &app));
                }
                let v = force_meta(&self.g, v);
                if matches!(v, Val::Neutral(Head::Meta(_), _)) {
                    // A number whose type isn't decided yet: its value's
                    // range, as for a branch (D135), once another value
                    // decides it is a number.
                    if let Some(n) = self.known_int(cx, &a.tm).filter(|_| matches!(q.head(), Tm::Meta(x) if *x == m)) {
                        constants.push(n);
                    }
                    continue;
                }
                found = Some(match found {
                    None => v,
                    Some(j) => self.join_types(&j, &v),
                });
            }
            if let Some(j) = &mut found {
                for n in constants {
                    let c = self.range_type(super::interval::Range::exact(n));
                    *j = self.join_types(j, &c);
                }
            }
            if let (Some(t), Some(j)) = (target, found) {
                let _ = unify(&self.g, cx.lvl(), &t, &j);
            }
        }
        for a in args {
            // What the value gave its own type, before an unknown one is
            // solved to its parameter's below.
            let before = self.peel(&a.own);
            if !self.unify_at(cx, &a.dom, &a.own, a.span, "this expression") {
                continue;
            }
            if let Some(g) = self.refined_mismatch(cx, &a.dom, &a.own, a.span) {
                self.report_gained(cx, &a.dom, &a.own, &g, a.span, "this expression");
                continue;
            }
            // A class's type with a base type (#360): only its own values.
            if crate::core::class_type_base(&self.g, &a.dom).is_some() {
                self.check_based(cx, &a.dom, Some(&a.own), a.span);
                continue;
            }
            // A refinement the value's own type doesn't already give it
            // (D71): as `check` asks of a value checked against it.
            if let Some((d, dargs)) = self.refined_alias(&a.dom) {
                let already = self.refined_alias(&before).is_some_and(|(d2, _)| d2 == d);
                let within = self.is_range(&a.dom)
                    && match (self.type_range(&a.dom), self.type_range(&before)) {
                        (Some(j), Some(r)) => j.holds(r),
                        _ => false,
                    };
                if !already && !within {
                    let v = self.eval(cx, &a.tm);
                    self.refined_obligation(cx, d, dargs, v, a.span);
                }
            }
        }
    }

    /// A call of a function with `comptime` parameters (D59): it must be
    /// complete, and each such argument known at compile time.
    fn check_comptime_call(&mut self, cx: &Cx, t: &Tm, args: &[&Expr], span: Span) -> bool {
        let (h, spine) = t.spine();
        let Tm::Def(d) = h else { return true };
        let ct = self.g.defs[d.0 as usize].comptime.clone();
        if ct.is_empty() {
            return true;
        }
        let mut ok = true;
        let name = self.g.defs[d.0 as usize].name.to_string();
        let (n_implicit, inner) = self.fn_meta.get(d).map(|m| (m.n_implicit, m.inner.clone())).unwrap_or_default();
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
                        .with_help("it is expanded where it is called; wrap the call in a lambda to pass it as a value, e.g. `\\x -> f 2 x`"),
                );
                return false;
            };
            if !self.tm_static(cx, arg, 0, cx.lvl()) {
                let k = super::expl_index(n_implicit, &inner, b).unwrap_or(0);
                let pname = self.fn_meta.get(d).and_then(|m| m.params.get(k)).map(|p| p.0.clone()).unwrap_or_default();
                let at = args.get(k).map(|a| a.span).unwrap_or(span);
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

    /// The conditions on a type's parameters, for its application to `env`
    /// at `span` (#136).
    pub fn oblige_ty_conds(&mut self, cx: &Cx, span: Span, tid: TyId, env: Vec<Val>) {
        let Some(conds) = self.ty_conds.get(&tid).cloned() else { return };
        let ty = self.g.tys[tid.0 as usize].name.to_string();
        let written = self.src_text(span);
        for p in &conds {
            let goal = self.inst_pred(p, env.clone());
            let kind = ObKind::TypeParams { ty: ty.clone(), written: written.clone() };
            self.oblige(cx, span, kind, p.text.clone(), goal, None);
        }
    }

    /// Preconditions of a call and invariants of a constructor application (§7.1).
    fn call_obligations(&mut self, cx: &Cx, t: &Tm, span: Span, head_span: Span, typed: bool) {
        let (h, args) = t.spine();
        let args: Vec<Rc<Tm>> = args.into_iter().cloned().collect();
        match h {
            Tm::Def(d) => {
                // A class's function: its dictionary may be found through a
                // refinement alias (#226).
                if self.class_methods.contains(d) && self.in_spec == 0 && self.in_proof == 0 {
                    self.class_calls.push(PendingPre { cx: cx.keep(), call: t.clone(), span, owner: self.cur_fn, in_spec: 0, typed: false });
                }
                // Only what is needed: most calls have no measure to compare
                // and no precondition, and evaluating their arguments for
                // nothing was much of the time this took.
                // Its type equations (#209), at this call's types.
                self.want_call_teqs(cx, *d, t, &args, span);
                let Some(spec) = self.specs.get(d) else { return };
                let (n, measured, pres) = (spec.n_binders, spec.measure.is_some(), spec.preds.iter().any(|p| !p.is_post));
                if args.len() >= n {
                    let caller_measured = self.cur_fn.and_then(|c| self.specs.get(&c)).is_some_and(|s| s.measure.is_some());
                    if measured && caller_measured {
                        let env: Vec<Val> = args[..n].iter().map(|a| self.eval(cx, a)).collect();
                        self.measure_obligation(cx, *d, &env, span, head_span);
                    } else {
                        self.saturated_heads.insert(head_span);
                        if !measured && !caller_measured {
                            self.note_rec_call(cx, *d, &args[..n], span);
                        }
                    }
                }
                if !pres {
                    return;
                }
                let spec = self.specs[d].clone();
                let name = self.g.defs[d.0 as usize].name.to_string();
                // A class's function: at a known instance whose function has
                // a signature of its own, that signature's preconditions
                // (#225), partially applied too (#252). Which instance is
                // known once the dictionaries are found, at the end of the
                // module.
                if self.class_methods.contains(d) {
                    self.pending_class_pres.push(PendingPre { cx: cx.keep(), call: t.clone(), span, owner: self.cur_fn, in_spec: self.in_spec, typed });
                    return;
                }
                if args.len() < spec.n_binders {
                    self.partial_pre_obligations(cx, *d, &name, &args, span);
                    return;
                }
                self.pre_obligations(cx, *d, &name, &args, t, span);
            }
            Tm::TyCon(tid) => {
                // Its type equations (#209), outside a signature (which
                // asks them of its result's type only).
                if self.ty_cond_defer.is_none() && args.len() >= self.g.tys[tid.0 as usize].params.len() {
                    if let Some(teqs) = self.ty_teqs.get(tid).cloned() {
                        let env: Vec<Val> = args.iter().map(|a| self.eval(cx, a)).collect();
                        for q in teqs {
                            self.want_type_teq(cx, *tid, &env, &q, span);
                        }
                    }
                }
                // Wherever a type is applied, its conditions on its
                // parameters must hold (#136).
                if !self.ty_conds.contains_key(tid) || args.len() < self.g.tys[tid.0 as usize].params.len() {
                    return;
                }
                let env: Vec<Val> = args.iter().map(|a| self.eval(cx, a)).collect();
                if let Some(d) = &mut self.ty_cond_defer {
                    d.push((span, *tid, env));
                    return;
                }
                self.oblige_ty_conds(cx, span, *tid, env);
            }
            Tm::Con(c) => {
                self.want_con_teqs(cx, *c, &args, span);
                let Some(invs) = self.con_invs.get(c).cloned() else { return };
                if args.len() < self.g.arity_con(*c) {
                    return;
                }
                let env: Vec<Val> = args.iter().map(|a| self.eval(cx, a)).collect();
                let name = self.g.cons[c.0 as usize].name.to_string();
                for p in &invs {
                    if let Some((k, _)) = p.alias {
                        if env.get(k).is_some_and(|a| self.nat_pred_holds(cx, p, a)) {
                            continue;
                        }
                    }
                    let goal = self.inst_pred(p, env.clone());
                    self.oblige(cx, span, ObKind::Invariant { con: name.clone() }, p.text.clone(), goal, None);
                }
            }
            Tm::Var(_) => {
                // A local defined as a class's function (#252): a call of
                // it is a call of the class's function; a partial one, a
                // use of it as a value.
                if let Some((m, f, call, saturated)) = self.class_use(cx, t) {
                    if saturated {
                        self.class_local_calls.push((m, PendingPre { cx: cx.keep(), call, span, owner: self.cur_fn, in_spec: 0, typed: false }));
                    } else {
                        self.class_value_uses.push((m, f, span, false));
                    }
                }
            }
            _ => {}
        }
    }

    /// The preconditions of `d` partially applied to `args` (D86) that are
    /// about those arguments alone; the others are in its type
    /// (`refined_fn_type`).
    fn partial_pre_obligations(&mut self, cx: &Cx, d: DefId, name: &str, args: &[Rc<Tm>], span: Span) {
        let Some(spec) = self.specs.get(&d).cloned() else { return };
        let given = args.len();
        let total = spec.n_binders + 1;
        let now = spec.preds.iter().filter(|p| !p.is_post && !mentions_level_from(&p.tm, total, given, 0));
        let mut env: Vec<Val> = args.iter().map(|a| self.eval(cx, a)).collect();
        for k in given..total {
            env.push(Val::var(usize::MAX / 2 + k));
        }
        for p in now {
            let goal = self.inst_pred(p, env.clone());
            self.oblige(cx, span, ObKind::Pre { callee: name.to_string() }, p.text.clone(), goal, None);
        }
    }

    /// `t` as a class's function applied to its dictionary, an unknown
    /// (#252): itself, or a local defined as one applied to arguments.
    /// The unknown, the class's function, the application, and whether it
    /// has all the function's arguments.
    pub(super) fn class_use(&self, cx: &Cx, t: &Tm) -> Option<(MetaId, DefId, Tm, bool)> {
        if self.in_spec > 0 || self.in_proof > 0 {
            return None;
        }
        let (m, term) = match t.head() {
            Tm::Def(f) => {
                let lay = self.method_layout(*f)?;
                let (_, args) = t.spine();
                let Tm::Meta(m) = args.get(lay.dict)?.head() else { return None };
                (*m, t.clone())
            }
            Tm::Var(i) => {
                let l = cx.lvl().checked_sub(i + 1)?;
                if cx.locals.get(l)?.bound {
                    return None;
                }
                let Val::Neutral(Head::Def(f), sp) = &cx.env[l] else { return None };
                let lay = self.method_layout(*f)?;
                let Some(Elim::App(Val::Neutral(Head::Meta(m), dsp), _)) = sp.get(lay.dict) else { return None };
                if !dsp.is_empty() {
                    return None;
                }
                (*m, quote(&self.g, cx.lvl(), &self.eval(cx, t)))
            }
            _ => return None,
        };
        let (Tm::Def(f), args) = term.spine() else { return None };
        if !self.class_methods.contains(f) {
            return None;
        }
        let saturated = args.len() >= self.method_layout(*f)?.arity;
        Some((m, *f, term.clone(), saturated))
    }

    /// Is `h` an instance's function with a signature of its own (#225),
    /// in its instance's dictionary?
    fn refined_in_dict(&self, h: &Tm) -> bool {
        matches!(h, Tm::Def(d) if self.refined_inst_fns.contains(d))
            && self.cur_fn.is_some_and(|f| self.g.well_known.dict_fns.contains(&f))
    }

    /// A call `t` of a class's function with all its arguments, where the
    /// dictionary is a known instance's whose function has a signature of
    /// its own (#289): that function's result type at the call's
    /// arguments, as a value of it would give (`instance_value`). `None`
    /// otherwise, where the instance isn't known yet (the class's result
    /// type then, with what the class promises checked at the call once it
    /// is: `known_result_obligations`), or where the dictionary is found
    /// through a refinement alias.
    fn instance_call_type(&mut self, cx: &Cx, t: &Tm) -> Option<Val> {
        let Tm::Def(d) = t.head() else { return None };
        if !self.class_methods.contains(d) || self.refined_inst_fns.is_empty() || self.in_spec > 0 || self.in_proof > 0 {
            return None;
        }
        let Some((m, _, _, true)) = self.class_use(cx, t) else { return None };
        if !self.inst_reqs.is_empty() {
            self.solve_instances(false);
            self.retry_waiting(false);
        }
        // Through a refinement alias (`Nat`'s dictionary is `Int`'s), the
        // class's result type at the alias, checked as such (#226).
        if self.alias_dicts.iter().any(|a| a.meta == Some(m)) {
            return None;
        }
        let call = crate::core::zonk_metas(&self.g, cx.lvl(), t);
        let direct = crate::native::ir::known_instance(&self.g, &call)?;
        let (Tm::Def(f), iargs) = direct.spine() else { return None };
        if !self.refined_inst_fns.contains(f) {
            return None;
        }
        let mut ty = eval(&self.g, &Rc::new(Vec::new()), &self.g.defs[f.0 as usize].ty);
        for a in iargs {
            let Val::Pi(_, _, _, _, c) = self.force(&ty) else { return None };
            ty = apply_closure(&self.g, &c, self.eval(cx, a));
        }
        (!matches!(self.force(&ty), Val::Pi(..))).then_some(ty)
    }

    /// The preconditions of `d`, called with `args` (at least its binders)
    /// as `t`; `name` is the callee as shown.
    fn pre_obligations(&mut self, cx: &Cx, d: DefId, name: &str, args: &[Rc<Tm>], t: &Tm, span: Span) {
        let Some(spec) = self.specs.get(&d).cloned() else { return };
        let mut env: Vec<Val> = args[..spec.n_binders].iter().map(|a| self.eval(cx, a)).collect();
        env.push(self.eval(cx, t));
        for p in spec.preds.iter().filter(|p| !p.is_post) {
            if let Some((k, _)) = p.alias {
                if env.get(k).is_some_and(|a| self.nat_pred_holds(cx, p, a)) {
                    continue;
                }
            }
            let goal = self.inst_pred(p, env.clone());
            self.oblige(cx, span, ObKind::Pre { callee: name.to_string() }, p.text.clone(), goal, None);
        }
    }

    /// The preconditions of calls of classes' functions, once their
    /// dictionaries are found (#225): at a known instance whose function
    /// has a signature of its own, its preconditions; otherwise the
    /// class's.
    pub(super) fn class_call_obligations(&mut self) {
        let pending = std::mem::take(&mut self.pending_class_pres);
        let saved = (self.cur_fn, self.in_spec);
        for PendingPre { cx, call, span, owner, in_spec, typed } in pending {
            (self.cur_fn, self.in_spec) = (owner, in_spec);
            let cx = cx.cx();
            let call = crate::core::zonk_metas(&self.g, cx.lvl(), &call);
            let (h, args) = call.spine();
            let Tm::Def(d) = h else { continue };
            let name = self.g.defs[d.0 as usize].name.to_string();
            let args: Vec<Rc<Tm>> = args.into_iter().cloned().collect();
            if self.specs.get(d).is_some_and(|s| args.len() < s.n_binders) {
                // Partially applied (#252): the instance's preconditions
                // about the arguments given, at a known instance whose
                // function has a signature of its own.
                match self.instance_value(&cx, &call) {
                    Some((direct, _)) => {
                        let (Tm::Def(f), iargs) = direct.spine() else { continue };
                        let iargs: Vec<Rc<Tm>> = iargs.into_iter().cloned().collect();
                        self.partial_pre_obligations(&cx, *f, &name, &iargs, span);
                    }
                    None => {
                        let d = *d;
                        self.partial_pre_obligations(&cx, d, &name, &args, span);
                    }
                }
                continue;
            }
            let direct = crate::native::ir::known_instance(&self.g, &call);
            if let Some(direct) = direct {
                let (ih, iargs) = direct.spine();
                if let Tm::Def(f) = ih {
                    if self.refined_inst_fns.contains(f) && self.specs.get(f).is_some_and(|s| iargs.len() >= s.n_binders) {
                        let iargs: Vec<Rc<Tm>> = iargs.into_iter().cloned().collect();
                        self.pre_obligations(&cx, *f, &name, &iargs, &direct, span);
                        if !typed {
                            self.known_result_obligations(&cx, *d, *f, &args, &iargs, &call, span);
                        }
                        continue;
                    }
                }
            }
            let d = *d;
            self.pre_obligations(&cx, d, &name, &args, &call, span);
        }
        (self.cur_fn, self.in_spec) = saved;
    }

    /// A call `call` of class function `d` (its arguments `args`) at a
    /// known instance whose function `f` (its arguments `iargs`) has a
    /// signature of its own: the call checked `f`'s preconditions, so the
    /// class's refined result type holds only where the class's
    /// preconditions do too. Elsewhere, each refinement in the class's
    /// result type that the instance's result type doesn't have must
    /// follow from what is known of the call (the instance's signature at
    /// its arguments).
    #[allow(clippy::too_many_arguments)]
    fn known_result_obligations(&mut self, cx: &Cx, d: DefId, f: DefId, args: &[Rc<Tm>], iargs: &[Rc<Tm>], call: &Tm, span: Span) {
        let Some(spec) = self.specs.get(&d).cloned() else { return };
        let pres: Vec<_> = spec.preds.iter().filter(|p| !p.is_post).cloned().collect();
        if pres.is_empty() || args.len() < spec.n_binders {
            return;
        }
        // The result's type at these arguments: the class's, the instance's.
        let at = |e: &Self, def: DefId, args: &[Rc<Tm>]| -> Option<(Val, Vec<(Name, Val)>)> {
            let mut ty = eval(&e.g, &Rc::new(Vec::new()), &e.g.defs[def.0 as usize].ty);
            let mut doms = Vec::new();
            for a in args {
                let Val::Pi(x, _, _, dom, c) = e.force(&ty) else { return None };
                doms.push((x.clone(), (*dom).clone()));
                ty = apply_closure(&e.g, &c, e.eval(cx, a));
            }
            (!matches!(e.force(&ty), Val::Pi(..))).then_some((ty, doms))
        };
        let (Some((cty, doms)), Some((ity, _))) = (at(self, d, args), at(self, f, iargs)) else { return };
        let lvl = cx.lvl();
        let env = cx.env.to_vec();
        // `None`: a refinement under a recursive type, which a call can't
        // be shown to give but where the class's preconditions hold.
        let goals = self.alias_goals_pub(&env, call, &cty, &ity);
        if goals.as_ref().is_some_and(|g| g.is_empty()) {
            return;
        }
        // Where the class's preconditions hold, the instance's signature
        // refines the class's (E0371): nothing to prove.
        let mut penv: Vec<Val> = args[..spec.n_binders].iter().map(|a| self.eval(cx, a)).collect();
        penv.push(self.eval(cx, call));
        let mut held = self.bool_lit(true);
        for p in pres.iter().rev() {
            let v = self.inst_pred(p, penv.clone());
            held = self.if_tm(quote(&self.g, lvl, &v), held, self.bool_lit(false));
        }
        // The class's preconditions at the call's arguments (`-5 > 0`).
        let names: Vec<(String, String)> = doms
            .iter()
            .zip(&penv)
            .filter(|((x, _), _)| x.as_ref() != "_")
            .map(|((x, _), v)| {
                let shown = self.show_val(cx, v);
                (x.to_string(), if shown.contains(' ') { format!("({shown})") } else { shown })
            })
            .collect();
        let pre_text = pres.iter().map(|p| format!("`{}`", rename_words(&p.text, &names))).collect::<Vec<_>>().join(" and ");
        let call_text = self.src_text(span);
        let member = self.g.defs[d.0 as usize].name.rsplit('.').next().unwrap_or_default().to_string();
        // The instance, as its dictionary's type shows it (`Pos Box`).
        let inst = doms.iter().find_map(|(_, t)| match self.force(t) {
            Val::TyCon(c, _) if self.class_defs.contains_key(&c) => Some(self.show_val(cx, t)),
            _ => None,
        });
        let inst = inst.unwrap_or_default();
        let Some(goals) = goals else {
            let kind = ObKind::KnownResult { call: call_text, alias: self.show_val(cx, &cty), inside: false, pres: pre_text.clone(), inst, member };
            let goal = self.eval(cx, &held);
            self.oblige(cx, span, kind, pre_text.replace('`', ""), goal, None);
            return;
        };
        for (g, text, alias, inside) in goals {
            let text = if inside {
                text
            } else {
                let subject = self.alias_subject.get(&alias).map(|s| s.to_string()).unwrap_or_default();
                rename_words(&text, &[(subject, if call_text.contains(' ') { format!("({call_text})") } else { call_text.clone() })])
            };
            let goal = self.if_tm(held.clone(), self.bool_lit(true), g);
            let goal = self.eval(cx, &goal);
            let kind = ObKind::KnownResult {
                call: call_text.clone(),
                alias: self.g.defs[alias.0 as usize].name.to_string(),
                inside,
                pres: pre_text.clone(),
                inst: inst.clone(),
                member: member.clone(),
            };
            self.oblige(cx, span, kind, text, goal, None);
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

    /// `forall x y : …` (D137), allowed only in a named precondition: a Π
    /// over its variables whose body is its premises implying its conclusion.
    pub fn elab_forall(&mut self, cx: &mut Cx, e: &Expr) -> (Tm, Val) {
        let ExprKind::Forall(vs, cs) = &e.kind else { return (Tm::Error, Val::Error) };
        if self.forall_ok == 0 {
            self.err(
                Diagnostic::error("E0289", "`forall` is only allowed in a named precondition or a lemma's `ensures`", e.span)
                    .with_help("write it as a precondition with a name, `name: forall …`, and use it in the body with `have name …`"),
            );
            return (Tm::Error, Val::Error);
        }
        let n0 = cx.lvl();
        let mut tys = Vec::new();
        for v in vs {
            let written = cs.iter().find_map(|c| match c {
                Constraint::Typed { name, ty, .. } if name.name == v.name => Some(ty),
                _ => None,
            });
            let saved = cx.type_pos;
            cx.type_pos = true;
            let ty = match written {
                Some(t) => self.elab_type(cx, t),
                None => self.fresh_meta(cx),
            };
            cx.type_pos = saved;
            let tv = self.eval(cx, &ty);
            let l = cx.bind(&v.name, tv, Mult::Many);
            self.bound_at(cx, l, v.span);
            tys.push((Rc::from(v.name.as_str()), ty));
        }
        let b = self.bool_ty();
        let saved_facts = cx.facts.len();
        let mut preds = Vec::new();
        for c in cs {
            match c {
                Constraint::Typed { name, .. } => {
                    if !vs.iter().any(|v| v.name == name.name) {
                        self.err(Diagnostic::error("E0355", format!("`{}` is not a variable of this `forall`", name.name), name.span));
                    }
                }
                Constraint::Pred(p) | Constraint::Named(_, p) => {
                    let t = self.check(cx, p, &b, false);
                    let v = self.eval(cx, &t);
                    cx.assume(v);
                    preds.push(t);
                }
            }
        }
        cx.facts.truncate(saved_facts);
        cx.truncate(n0);
        let Some(concl) = preds.pop() else {
            self.err(
                Diagnostic::error("E0289", "this `forall` has no conclusion", e.span)
                    .with_help("its last clause is what holds for all of its variables, e.g. `forall x : x~a, le x x`"),
            );
            return (Tm::Error, Val::Error);
        };
        let mut body = concl;
        for p in preds.into_iter().rev() {
            body = self.if_tm(p, body, self.bool_lit(true));
        }
        for (n, ty) in tys.into_iter().rev() {
            body = Tm::Pi(n, Mult::Many, Icit::Expl, Rc::new(ty), Rc::new(body));
        }
        (Tm::PrimApp(Prim::Forall, vec![body]), b)
    }

    /// `have h a b …` for a named precondition `h` (D137): its `forall`s'
    /// variables filled in, left to right, the rest a fact.
    fn have_hyp(&mut self, cx: &mut Cx, e: &Expr, name: &str, fact: Val, args: &[&Expr]) {
        let mut args = args.to_vec();
        args.reverse();
        let t = quote(&self.g, cx.lvl(), &fact);
        let mut unfilled = false;
        let r = self.fill_forall(cx, &t, &mut args, &mut unfilled);
        if !args.is_empty() {
            self.err(
                Diagnostic::error("E0290", format!("`{name}` has fewer variables than the values given here"), e.span)
                    .with_help(format!("give one value for each variable of `{name}`'s `forall`s, left to right")),
            );
            return;
        }
        if unfilled {
            self.err(
                Diagnostic::error("E0290", format!("`have {name}` needs a value for each variable of its `forall`s"), e.span)
                    .with_help("a `forall` is used by filling in its variables: the fact is then what it says of those values"),
            );
            return;
        }
        let v = self.eval(cx, &r);
        cx.assume(v);
    }

    fn fill_forall(&mut self, cx: &mut Cx, t: &Tm, args: &mut Vec<&Expr>, unfilled: &mut bool) -> Tm {
        match t {
            Tm::PrimApp(Prim::Forall, xs) if xs.len() == 1 => {
                let mut v = self.eval(cx, &xs[0]);
                loop {
                    match self.force(&v) {
                        Val::Pi(_, _, _, dom, clo) => {
                            let Some(a) = args.pop() else {
                                *unfilled = true;
                                return t.clone();
                            };
                            let at = self.check(cx, a, &dom, false);
                            let av = self.eval(cx, &at);
                            v = apply_closure(&self.g, &clo, av);
                        }
                        other => {
                            let body = quote(&self.g, cx.lvl(), &other);
                            return self.fill_forall(cx, &body, args, unfilled);
                        }
                    }
                }
            }
            Tm::Case(s, c) if c.branches.len() == 2 && c.lits.is_empty() && c.default.is_none() => {
                let lit = |x: &Tm| match x {
                    Tm::ConApp(k, v) if v.is_empty() => Some(Some(*k) == self.g.well_known.true_con),
                    _ => None,
                };
                let (tc, fc) = (self.g.well_known.true_con, self.g.well_known.false_con);
                let br = |con: Option<ConId>| c.branches.iter().find(|(k, _, _)| Some(*k) == con).map(|b| b.2.clone());
                let (Some(tb), Some(fb)) = (br(tc), br(fc)) else { return t.clone() };
                let (s2, tb2, fb2) = match (lit(&tb), lit(&fb)) {
                    // `a and b`
                    (_, Some(false)) => (self.fill_forall(cx, s, args, unfilled), self.fill_forall(cx, &tb, args, unfilled), fb),
                    // `a implies b`
                    (_, Some(true)) => ((**s).clone(), self.fill_forall(cx, &tb, args, unfilled), fb),
                    // `a or b`
                    (Some(true), _) => (self.fill_forall(cx, s, args, unfilled), tb, self.fill_forall(cx, &fb, args, unfilled)),
                    _ => return t.clone(),
                };
                self.if_tm(s2, tb2, fb2)
            }
            _ => t.clone(),
        }
    }

    /// A lemma's conclusion `t` (its value `v`), if a `forall`, with its
    /// variables bound in `cx` and its premises assumed: what remains to
    /// prove (D146).
    pub fn intro_forall(&mut self, cx: &mut Cx, t: &Tm, v: Val) -> Val {
        let Tm::PrimApp(Prim::Forall, xs) = t else { return v };
        let [pi] = xs.as_slice() else { return v };
        let mut body = pi.clone();
        while let Tm::Pi(name, _, _, dom, b) = &body {
            let dv = self.eval(cx, dom);
            cx.bind(name, dv, Mult::Many);
            body = (**b).clone();
        }
        // `p implies q`: assume `p`, prove `q`.
        let true_con = self.g.well_known.true_con;
        loop {
            let next = match &body {
                Tm::Case(s, c) if c.branches.len() == 2 && c.lits.is_empty() && c.default.is_none() => {
                    let br = |k: Option<ConId>| c.branches.iter().find(|b| Some(b.0) == k).map(|b| b.2.clone());
                    match (br(true_con), br(self.g.well_known.false_con)) {
                        (Some(tb), Some(Tm::ConApp(k, a))) if Some(k) == true_con && a.is_empty() => {
                            let p = self.eval(cx, s);
                            cx.assume(p);
                            Some(tb)
                        }
                        _ => None,
                    }
                }
                _ => None,
            };
            match next {
                Some(b) => body = b,
                None => break,
            }
        }
        self.eval(cx, &body)
    }

    /// `have e` (D49): a lemma's conclusion, or a proven `Bool`, becomes a fact.
    pub fn have(&mut self, cx: &mut Cx, e: &Expr) {
        // A named precondition (D137).
        {
            let mut args = Vec::new();
            let mut h = e;
            while let ExprKind::App(f, a) = &h.kind {
                args.push(&**a);
                h = f;
            }
            args.reverse();
            if let ExprKind::Var(n) = &h.kind {
                if cx.lookup(n).is_none() {
                    if let Some((_, fact)) = self.cur_hyps.iter().find(|(x, _)| x == n).cloned() {
                        self.have_hyp(cx, e, n, fact, &args);
                        return;
                    }
                }
            }
        }
        // `have l a b x y` (D146): the lemma's arguments, then values for
        // its conclusion's `forall`.
        let (inner, extra) = self.forall_lemma_args(cx, e);
        let e = inner;
        let (t, ty) = self.infer(cx, e);
        let h = t.head();
        if let Tm::Def(d) = h {
            if let Some(spec) = self.specs.get(d).cloned() {
                if let Some(ens) = &spec.ensures {
                    let args = t.spine().1;
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
                    if !extra.is_empty() {
                        let name = self.g.defs[d.0 as usize].name.to_string();
                        self.have_hyp(cx, e, &name, fact, &extra);
                        return;
                    }
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

    /// `have x~T` (D170): `x`'s type is `T`. Checking `x` against `T` settles
    /// what is still unknown of its type (a literal's, before it would
    /// become a `Nat`), and a refinement `T` adds is an obligation, then
    /// facts.
    fn have_type(&mut self, cx: &mut Cx, x: &Ident, ty: &Expr) {
        let t = self.elab_type(cx, ty);
        let tv = self.eval(cx, &t);
        let var = Expr { kind: ExprKind::Var(x.name.clone()), span: x.span };
        let saved = self.post_target.take();
        let xt = self.check(cx, &var, &tv, false);
        self.post_target = saved;
        if matches!(xt, Tm::Error) {
            return;
        }
        let xv = self.eval(cx, &xt);
        for (fact, _, _) in self.alias_facts(cx, cx.lvl(), &t, xv) {
            cx.assume(fact);
        }
    }

    /// `l a b x y` for a lemma `l` of two parameters that concludes a
    /// `forall`: `l a b`, and `[x, y]` (D146). Otherwise `e` and none.
    fn forall_lemma_args<'e>(&self, cx: &Cx, e: &'e Expr) -> (&'e Expr, Vec<&'e Expr>) {
        let mut spine = Vec::new();
        let mut h = e;
        while let ExprKind::App(f, a) = &h.kind {
            spine.push(h);
            let _ = a;
            h = f;
        }
        let sym = match &h.kind {
            ExprKind::Var(x) if cx.lookup(x).is_none() => self.resolve(x, false),
            ExprKind::Field(q, x) => match &q.kind {
                ExprKind::Var(q) if cx.lookup(q).is_none() => self.qualifier(q).and_then(|m| self.resolve_qualified(&m, &x.name, false)),
                _ => None,
            },
            _ => None,
        };
        let Some(Sym::Def(d)) = sym else { return (e, Vec::new()) };
        let Some(spec) = self.specs.get(&d) else { return (e, Vec::new()) };
        let concludes_forall = spec.ensures.as_ref().is_some_and(|p| matches!(p.tm, Tm::PrimApp(Prim::Forall, _)));
        let n = spec.n_binders - spec.n_implicit - spec.inner.len();
        if !concludes_forall || spine.len() <= n {
            return (e, Vec::new());
        }
        // `spine` is outermost first: the last `spine.len() - n` applications
        // give the extra values.
        let extra_n = spine.len() - n;
        let inner = match &spine[extra_n - 1].kind {
            ExprKind::App(f, _) => &**f,
            _ => e,
        };
        let mut extra: Vec<&Expr> = spine[..extra_n]
            .iter()
            .filter_map(|x| match &x.kind {
                ExprKind::App(_, a) => Some(&**a),
                _ => None,
            })
            .collect();
        extra.reverse();
        (inner, extra)
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
    /// A later argument that is a call whose type can't be read that way
    /// (its result type mentions its arguments: `find b i`) is checked here,
    /// before the function, into `ready`, so it too is checked only once.
    fn look_ahead(
        &mut self,
        cx: &mut Cx,
        t: Tm,
        ty: Val,
        args: &[&Expr],
        head_name_span: Span,
        ready: &mut HashMap<usize, (Tm, Val)>,
    ) -> (Tm, Val) {
        let (t, ty) = self.insert(cx, t, ty);
        let mut r = ty.clone();
        let mut first_fn = None;
        for (k, a) in args.iter().enumerate() {
            let Val::Pi(_, _, Icit::Expl, dom, c) = self.force(&r) else { break };
            if first_fn.is_none() && (matches!(a.kind, ExprKind::Lambda(..)) || matches!(self.force(&dom), Val::Pi(..))) {
                first_fn = Some(k);
            }
            if first_fn.is_some_and(|f| k > f) {
                let q = quote(&self.g, cx.lvl() + k, &dom);
                // Only an argument whose parameter's type doesn't depend on
                // the ones before it can be checked out of order.
                if !mentions_level_from(&q, cx.lvl() + k, cx.lvl(), 0) {
                    if let Some(aty) = self.shallow_type(cx, a) {
                        let _ = unify(&self.g, cx.lvl(), &dom, &aty);
                    } else if matches!(a.kind, ExprKind::App(..)) && !matches!(self.force(&dom), Val::Pi(..)) {
                        self.alias_covered = self.head_checks_aliases && self.is_direct_alias(&dom);
                        self.name_span = head_name_span;
                        let at = self.check(cx, a, &dom, false);
                        let av = self.eval(cx, &at);
                        ready.insert(k, (at, av));
                    }
                }
            }
            r = apply_closure(&self.g, &c, Val::var(cx.lvl() + k));
        }
        (t, ty)
    }

    /// The type of `a`, if it can be read without elaborating `a`: a local,
    /// or a call of a global function whose result type doesn't depend on
    /// its arguments (`string.chars s` is a `List Char`). `look_ahead` uses
    /// it so a lambda before `a` sees `a`'s type, refinement included.
    fn shallow_type(&self, cx: &Cx, a: &Expr) -> Option<Val> {
        let mut head = a;
        let mut n = 0;
        while let ExprKind::App(f, _) = &head.kind {
            head = f;
            n += 1;
        }
        if let ExprKind::Var(x) = &head.kind {
            if let Some(l) = cx.lookup(x) {
                return (n == 0).then(|| cx.locals[l].ty.clone());
            }
        }
        let sym = match &head.kind {
            ExprKind::Var(x) => self.resolve(x, false),
            ExprKind::Field(q, x) => match &q.kind {
                ExprKind::Var(q) if cx.lookup(q).is_none() => self.qualifier(q).and_then(|m| self.resolve_qualified(&m, &x.name, false)),
                _ => None,
            },
            _ => None,
        };
        let Some(Sym::Def(d)) = sym else { return None };
        let mut ty = &self.g.defs[d.0 as usize].ty;
        for _ in 0..n {
            match ty {
                Tm::Pi(_, _, Icit::Expl, _, b) => ty = b,
                _ => return None,
            }
        }
        let mut free = std::collections::BTreeSet::new();
        crate::core::free_vars(ty, 0, &mut free);
        if !free.is_empty() || matches!(ty, Tm::Error) {
            return None;
        }
        Some(eval(&self.g, &Rc::new(Vec::new()), ty))
    }

    /// An operand of an arithmetic or comparison operator: it takes the
    /// other operand's type, but not its refinement (`x < 10` with `x~Small`
    /// doesn't need `10` to be a `Small`; D71).
    /// An operand checked against `ty`, and its own type if it was
    /// inferred (an operand needn't have `ty`'s refinements, D71).
    fn check_operand(&mut self, cx: &mut Cx, e: &Expr, ty: &Val) -> (Tm, Option<Val>) {
        self.alias_covered = true;
        self.last_checked = None;
        let t = self.check(cx, e, ty, false);
        (t, self.last_checked.take())
    }

    pub fn apply_one(&mut self, cx: &mut Cx, t: Tm, ty: Val, a: &Expr) -> (Tm, Val) {
        self.apply_one_as(cx, t, ty, a, None, None, None)
    }

    /// The type a parameter whose refinements mention later parameters
    /// (#102) has at this call: the later arguments it needs are checked
    /// first, into `ready`, in order. `None` where one of their types
    /// depends on this argument; then it is checked against its type
    /// without the refinements, which asks more of it.
    #[allow(clippy::too_many_arguments)]
    fn late_expected(
        &mut self,
        cx: &mut Cx,
        t: Tm,
        ty: Val,
        k: usize,
        late: &Late,
        lates: &[Late],
        args: &[&Expr],
        ready: &mut HashMap<usize, (Tm, Val)>,
    ) -> (Tm, Val, Option<Val>) {
        let (t, ty) = self.insert(cx, t, ty);
        let Val::Pi(_, _, Icit::Expl, _, c) = self.force(&ty) else { return (t, ty, None) };
        let (_, spine) = t.spine();
        let mut env: Vec<Val> = spine.iter().map(|a| self.eval(cx, a)).collect();
        if env.len() != late.binder {
            return (t, ty, None);
        }
        env.push(Val::Error);
        let l = cx.lvl();
        let mut r = apply_closure(&self.g, &c, Val::var(l));
        // Levels from `l` on stand for arguments not checked here: this one,
        // and any other parameter between it and the last it needs whose own
        // refinements mention later parameters, which must be checked
        // against its refined type at its own turn, not its base type now.
        let mut unchecked = 1;
        let last = late.deps.iter().max().copied().unwrap_or(late.binder);
        for b in late.binder + 1..=last {
            let j = k + b - late.binder;
            let Val::Pi(_, _, Icit::Expl, dom, c) = self.force(&r) else { return (t, ty, None) };
            let Some(arg) = args.get(j) else { return (t, ty, None) };
            if !late.deps.contains(&b) && !ready.contains_key(&j) && lates.iter().any(|o| o.binder == b) {
                env.push(Val::Error);
                r = apply_closure(&self.g, &c, Val::var(l + unchecked));
                unchecked += 1;
                continue;
            }
            let av = match ready.get(&j) {
                Some((_, av)) => av.clone(),
                None => {
                    let q = quote(&self.g, l + unchecked, &dom);
                    if mentions_level_from(&q, l + unchecked, l, 0) {
                        return (t, ty, None);
                    }
                    self.alias_covered = self.head_checks_aliases && self.is_direct_alias(&dom);
                    let at = self.check(cx, arg, &dom, false);
                    let av = self.eval(cx, &at);
                    ready.insert(j, (at, av.clone()));
                    av
                }
            };
            env.push(av.clone());
            r = apply_closure(&self.g, &c, av);
        }
        env.resize(late.n, Val::Error);
        let expected = eval(&self.g, &Rc::new(env), &late.ty);
        (t, ty, Some(expected))
    }

    /// `apply_one`, checking the argument against `expected` instead of the
    /// parameter's type when given, or taking it as already checked
    /// (`ready`), and recording `elem` as the parameter a function value
    /// passed here is applied to elements of (#102).
    #[allow(clippy::too_many_arguments)]
    pub fn apply_one_as(
        &mut self,
        cx: &mut Cx,
        t: Tm,
        ty: Val,
        a: &Expr,
        expected: Option<Val>,
        elem: Option<ElemSub>,
        ready: Option<(Tm, Val)>,
    ) -> (Tm, Val) {
        let (t, ty) = self.insert(cx, t, ty);
        match self.force(&ty) {
            Val::Pi(_, m, Icit::Expl, dom, c) => {
                if let Some((at, av)) = ready {
                    return (Tm::App(Rc::new(t), Rc::new(at), Icit::Expl, m), apply_closure(&self.g, &c, av));
                }
                let dom = expected.unwrap_or((*dom).clone());
                // A refined function type's precondition (D84): required to
                // call the function.
                // A type's parameter's refinement is a condition on the type,
                // checked where it is applied to all its parameters (#136).
                let (head, prior) = t.spine();
                let ty_cond = matches!(head, Tm::TyCon(tid) if prior.len() + 1 == self.g.tys[tid.0 as usize].params.len());
                let pre = match self.refined_alias(&dom) {
                    Some((d, args)) if !ty_cond && !self.head_checks_aliases && self.is_direct_alias(&dom) && is_anon_alias(&self.g, d) => Some((d, args)),
                    _ => None,
                };
                self.alias_covered = (self.head_checks_aliases && self.is_direct_alias(&dom)) || pre.is_some();
                self.map_elem_sub = elem;
                let erased = m == Mult::Zero;
                self.in_erased += erased as usize;
                let at = self.check(cx, a, &dom, false);
                self.in_erased -= erased as usize;
                self.map_elem_sub = None;
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
            _ => {
                let shown = self.show_written(cx, &ty);
                let mut d = Diagnostic::error(
                    "E0205",
                    format!("too many arguments: this has type `{shown}`, which is not a function"),
                    a.span,
                )
                .with_label("extra argument");
                // `x -1`: a `-` glued to what follows is a sign (D169).
                if let (ExprKind::Neg(n), true) = (&a.kind, self.src_text(a.span).starts_with('-')) {
                    let operand = self.src_text(n.span);
                    d = d.with_help(format!(
                        "`-{operand}` is a negative argument, since its `-` is glued to it; to subtract, put a space after the `-`: `- {operand}`"
                    ));
                }
                self.err(d);
                (Tm::Error, Val::Error)
            }
        }
    }

    /// `a` as a strict part of parameter `p`, if condition `c` holds:
    /// `(p, c)`.
    fn part_of(&self, cx: &Cx, a: &Expr) -> Option<(usize, Option<u32>)> {
        match &a.kind {
            ExprKind::Var(n) => cx.lookup(n).and_then(|l| cx.locals[l].sub.map(|p| (p, cx.locals[l].sub_cond))),
            _ => None,
        }
    }

    /// `a` as parameter `p` itself (#109).
    fn param_itself(&self, cx: &Cx, a: &Expr) -> Option<usize> {
        match &a.kind {
            ExprKind::Var(n) => cx.lookup(n).and_then(|l| cx.locals[l].param),
            _ => None,
        }
    }

    /// `a` as parameter `p` or (unconditionally) a strict part of it.
    fn part_or_param(&self, cx: &Cx, a: &Expr) -> Option<usize> {
        match &a.kind {
            ExprKind::Var(n) => cx.lookup(n).and_then(|l| {
                let x = &cx.locals[l];
                if x.sub_cond.is_none() { x.sub.or(x.param) } else { x.param }
            }),
            _ => None,
        }
    }

    fn new_elem_cond(&mut self, alts: Vec<ElemAlt>) -> u32 {
        self.elem_conds.push(alts);
        (self.elem_conds.len() - 1) as u32
    }

    /// Argument `k` of a call of `d`: a function value there is applied to
    /// a strict part of the caller's parameter `p`, if `d` promises it to
    /// call that function only with parts of another argument, itself the
    /// parameter `p` or a part of it (#102). The promise is in `d`'s
    /// signature, as a precondition that is a membership, or read from its
    /// body where that is visible: in this module, or exported
    /// `transparent`. Whether it holds is decided once the module's bodies
    /// are checked, as a body may come after this call.
    fn elem_sub(&mut self, cx: &Cx, d: DefId, k: usize, args: &[&Expr]) -> Option<ElemSub> {
        let mut found: Option<(usize, Vec<ElemAlt>)> = None;
        // The argument E0301's help names: a part, rather than the parameter itself.
        let mut shown = None;
        for (j, aj) in args.iter().enumerate() {
            if j == k {
                continue;
            }
            let Some(p) = self.part_or_param(cx, aj) else { continue };
            let part = self.part_of(cx, aj).is_some();
            match &mut found {
                None => found = Some((p, vec![(d, k, j)])),
                Some((q, alts)) if *q == p => alts.push((d, k, j)),
                Some(_) => continue,
            }
            if shown.is_none_or(|(_, was_part): (usize, bool)| part && !was_part) {
                shown = Some((j, part));
            }
        }
        let (p, alts) = found?;
        let j = shown.map_or(alts[0].2, |(j, _)| j);
        let arg = self.src_text(args[j].span);
        let cond = self.new_elem_cond(alts);
        let head = self.arg_of.clone().unwrap_or_else(|| self.g.defs[d.0 as usize].name.to_string());
        self.elem_cond_at.insert(cond, (head, arg, j));
        Some(ElemSub { p, cond: Some(cond) })
    }

    /// Whether `d`'s body can be read for its promises (#102).
    pub fn body_visible(&self, d: DefId) -> bool {
        *self.g.defs[d.0 as usize].module == *self.cur || self.transparent.contains(&d)
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
                // A range (D135) isn't imposed on the other operand: they
                // share its base type. Each operand's range is its own.
                let left_literal = matches!(l.kind, ExprKind::Lit(ast::Lit::Int(_)));
                // An operator on a type with an instance of its class (D136,
                // M24): `+` is `Add.add`, `<=` is `Ord.le`. Numbers keep
                // their built-in operators.
                let early = if !left_literal && Self::class_op(op).is_some() {
                    let (lt, lty) = self.infer(cx, l);
                    // `lt` comes back if there is no class function: cloning
                    // it would copy every operator chained below it.
                    let lt = match self.class_operator(cx, op, lt, &lty, r, span) {
                        Ok(r) => return r,
                        Err(lt) => lt,
                    };
                    // The left side's type isn't known yet (`zero + x`): the right's.
                    if matches!(self.force(&lty), Val::Neutral(Head::Meta(_), _)) && !matches!(r.kind, ExprKind::Lit(_)) {
                        let (rt, rty) = self.infer(cx, r);
                        if self.has_class_operator(cx, op, &rty) {
                            if let Some(res) = self.class_operator_tms(cx, op, lt.clone(), rt.clone(), &rty, span) {
                                self.unify_at(cx, &rty, &lty, l.span, "this operand");
                                return res;
                            }
                        }
                        let shared = self.shared_operand_type(&rty);
                        self.unify_at(cx, &shared, &lty, l.span, "this operand");
                        self.operand_types = Some((lty.clone(), rty.clone()));
                        return self.finish_arith(cx, op, lt, rt, shared, l.span.to(r.span), span);
                    }
                    Some((lt, lty))
                } else {
                    None
                };
                let (lt, rt, lty, own) = if let Some((lt, lty)) = early {
                    let shared = self.shared_operand_type(&lty);
                    let (rt, rown) = self.check_operand(cx, r, &shared);
                    let rown = rown.unwrap_or_else(|| shared.clone());
                    (lt, rt, shared, (lty, rown))
                } else if left_literal && !matches!(r.kind, ExprKind::Lit(ast::Lit::Int(_))) {
                    let (rt, rty) = self.infer(cx, r);
                    let shared = self.shared_operand_type(&rty);
                    let (lt, lown) = self.check_operand(cx, l, &shared);
                    let lown = lown.unwrap_or_else(|| shared.clone());
                    (lt, rt, shared, (lown, rty))
                } else {
                    let (lt, lty) = self.infer(cx, l);
                    let shared = self.shared_operand_type(&lty);
                    let (rt, rown) = self.check_operand(cx, r, &shared);
                    let rown = rown.unwrap_or_else(|| shared.clone());
                    (lt, rt, shared, (lty, rown))
                };
                self.operand_types = Some(own);
                self.finish_arith(cx, op, lt, rt, lty, l.span.to(r.span), span)
            }
        }
    }

    /// The class and function an operator stands for on other types than
    /// numbers (M24): whether its operands are swapped, and whether the
    /// result is negated.
    fn class_op(op: Op) -> Option<(&'static str, &'static str, bool, bool)> {
        Some(match op {
            Op::Add => ("Add", "add", false, false),
            Op::Sub => ("Sub", "sub", false, false),
            Op::Mul => ("Mul", "mul", false, false),
            Op::Le => ("Ord", "le", false, false),
            Op::Ge => ("Ord", "le", true, false),
            Op::Lt => ("Ord", "le", true, true),
            Op::Gt => ("Ord", "le", false, true),
            _ => return None,
        })
    }

    /// The prelude class `class`'s function `method`, if `ty` has an
    /// instance of it (or a dictionary of it is in scope) and isn't a
    /// built-in number.
    pub(super) fn operator_method(&self, cx: &Cx, class: &str, method: &str, ty: &Val) -> Option<DefId> {
        let prelude = self.modules.get("std.prelude")?;
        let Some(Sym::Ty(ctid)) = prelude.types.get(class).copied() else { return None };
        if !self.class_defs.contains_key(&ctid) {
            return None;
        }
        let Some(Sym::Def(m)) = prelude.values.get(method).copied() else { return None };
        let t = self.force(ty);
        let found = match &t {
            Val::TyCon(id, _) if Some(*id) == self.g.well_known.int => false,
            Val::TyCon(id, _) => self.instances.contains_key(&(ctid, super::classes::HeadKey::Ty(*id))),
            Val::TupleTy(xs) if xs.is_empty() => self.instances.contains_key(&(ctid, super::classes::HeadKey::Unit)),
            Val::TupleTy(xs) if xs.len() >= 2 => self.instances.contains_key(&(ctid, super::classes::HeadKey::Pair)),
            Val::Neutral(Head::Meta(_), _) | Val::Error => false,
            // A class's type with the clause declared on it (#176).
            Val::Neutral(_, sp)
                if matches!(sp.last(), Some(Elim::Field(c, i)) if self.class_defs.get(&self.g.cons[c.0 as usize].ty).is_some_and(|cd| cd.clauses.iter().any(|(t, k, _)| t == i && *k == ctid))) =>
            {
                true
            }
            _ => {
                // A type parameter: a dictionary in scope.
                let tq = format!("{:?}", quote(&self.g, cx.lvl(), &t));
                cx.locals.iter().any(|loc| match self.force(&loc.ty) {
                    Val::TyCon(c, a) if c == ctid => a.last().is_some_and(|x| format!("{:?}", quote(&self.g, cx.lvl(), &self.force(x))) == tq),
                    _ => false,
                })
            }
        };
        found.then_some(m)
    }

    /// `l op r` through a class's function (M24), if `l`'s type has one.
    /// `lt` back if there is none.
    fn class_operator(&mut self, cx: &mut Cx, op: Op, lt: Tm, lty: &Val, r: &Expr, span: Span) -> Result<(Tm, Val), Tm> {
        self.find_type_dicts(lty);
        if !self.has_class_operator(cx, op, lty) {
            return Err(lt);
        }
        let rt = self.check(cx, r, lty, false);
        // Checking `r` can solve `lty`.
        if !self.has_class_operator(cx, op, lty) {
            return Err(lt);
        }
        self.class_operator_tms(cx, op, lt, rt, lty, span).ok_or(Tm::Error)
    }

    /// A class's type read from a dictionary not found yet (`Seq.Elem s`
    /// of a `Seq.uncons` just called): find the dictionaries the types
    /// known so far choose, so its operators are known (#176).
    pub(super) fn find_type_dicts(&mut self, ty: &Val) {
        let on_meta = matches!(self.force(ty), Val::Neutral(Head::Meta(_), sp) if sp.iter().any(|e| matches!(e, Elim::Field(..))));
        if on_meta && !self.inst_reqs.is_empty() {
            self.solve_instances(false);
            self.retry_waiting(false);
        }
    }

    /// Whether `op` on `ty` is a class's function (M24).
    fn has_class_operator(&mut self, cx: &Cx, op: Op, ty: &Val) -> bool {
        Self::class_op(op).is_some_and(|(class, method, _, _)| self.operator_method(cx, class, method, ty).is_some())
    }

    /// `lt op rt`, both of type `lty`, through a class's function (M24).
    fn class_operator_tms(&mut self, cx: &mut Cx, op: Op, lt: Tm, rt: Tm, lty: &Val, span: Span) -> Option<(Tm, Val)> {
        let (class, method, swap, negate) = Self::class_op(op)?;
        let m = self.operator_method(cx, class, method, lty)?;
        let (f, fty) = self.sym_term(cx, Sym::Def(m), span);
        self.name_span = span;
        let (f, fty) = self.insert(cx, f, fty);
        let (a, b) = if swap { (rt, lt) } else { (lt, rt) };
        let (f1, ty1) = self.apply_tm(cx, f, fty, a, lty, span);
        let (t, ty) = self.apply_tm(cx, f1, ty1, b, lty, span);
        if negate {
            let b = self.bool_ty();
            return Some((self.if_tm(t, self.bool_lit(false), self.bool_lit(true)), b));
        }
        Some((t, ty))
    }

    /// Apply `f : fty` to an elaborated argument `a : aty`.
    pub(super) fn apply_tm(&mut self, cx: &Cx, f: Tm, fty: Val, a: Tm, aty: &Val, span: Span) -> (Tm, Val) {
        match self.force(&fty) {
            Val::Pi(_, m, i, dom, c) => {
                self.unify_at(cx, &dom, aty, span, "this operand");
                let av = self.eval(cx, &a);
                let ty = apply_closure(&self.g, &c, av);
                (Tm::App(Rc::new(f), Rc::new(a), i, m), ty)
            }
            _ => (Tm::Error, Val::Error),
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
                        givens: self.givens.clone(),
                        ty: lty.clone(),
                        kind,
                        span: operands,
                        what: format!("`{}`", op.as_str()),
                        lvl: cx.lvl(),
                        names: cx.names(),
                        owner: self.cur_fn,
                    });
                }
                if op == Op::EqEq {
                    self.last_eq_ty = Some(lty.clone());
                }
                if matches!(op, Op::EqEq | Op::Ne) {
                    self.observe(operands, lty.clone());
                }
                // Compiled code never compares functions (D125).
                if matches!(op, Op::EqEq | Op::Ne) && self.in_spec == 0 && self.in_proof == 0 {
                    self.deferred.push(Deferred {
                        givens: self.givens.clone(),
                        ty: lty.clone(),
                        kind: OpClass::Comparable,
                        span: operands,
                        what: format!("`{}`", op.as_str()),
                        lvl: cx.lvl(),
                        names: cx.names(),
                        owner: self.cur_fn,
                    });
                }
                // Only the obligations need the operands' values: evaluating
                // the left operand walks every operator chained below it.
                match op {
                    Op::Sub => {
                        let (lv, rv) = (self.eval(cx, &lt), self.eval(cx, &rt));
                        let goal = Self::prim_val(Prim::Ge, vec![lv, rv]);
                        let text = self.src_text(span);
                        self.oblige(cx, span, ObKind::NatSub, text, goal, Some(lty.clone()));
                    }
                    Op::Div | Op::Rem => {
                        let rv = self.eval(cx, &rt);
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
                let result = match (result, class) {
                    (Some(r), _) => r,
                    // Arithmetic gives the operands' range, or their base
                    // number type (D134, D135).
                    (None, Some(OpClass::Numeric)) => {
                        let (a, b) = self.operand_types.take().unwrap_or_else(|| (lty.clone(), lty.clone()));
                        self.arith_result(cx, prim.clone(), &args[0], &args[1], &lty, &a, &b)
                    }
                    (None, _) => lty,
                };
                (Tm::PrimApp(prim, args), result)
            }
        }
    }

    // ── fields and qualified names ──────────────────────────────────────────

    /// `C.Name` without the types it is for (E0291).
    fn assoc_without_types(&mut self, tid: TyId, acc: DefId, class_span: Span, name: &Ident, span: Span) -> (Tm, Val) {
        self.index_sym(class_span, Sym::Ty(tid));
        self.index_sym(name.span, Sym::Def(acc));
        let Some(cd) = self.class_defs.get(&tid) else { return (Tm::Error, Val::Error) };
        let (cn, n) = (cd.name.clone(), name.name.clone());
        let d = if cd.params.len() == 1 {
            Diagnostic::error("E0291", format!("`{cn}.{n}` needs the type it is for"), span)
                .with_label(format!("each instance of `{cn}` gives its own `{n}`"))
                .with_help(format!("write `{cn}.{n} t` for the type `t`, e.g. `{cn}.{n} a` under a clause `{cn} a`"))
        } else {
            let ps = cd.params.join(" ");
            Diagnostic::error("E0291", format!("`{cn}.{n}` needs the {} types it is for", cd.params.len()), span)
                .with_label(format!("each instance of `{cn}` gives its own `{n}`"))
                .with_help(format!("write `{cn}.{n} {ps}` under a clause `{cn} {ps}`"))
        };
        self.err(d);
        (Tm::Error, Val::Error)
    }

    fn elab_field(&mut self, cx: &mut Cx, x: &Expr, name: &Ident, span: Span) -> (Tm, Val) {
        if Self::is_cursor(&name.name) {
            return self.note_member(cx, x);
        }
        // `Ord.le`: a class's function or lemma (D136).
        if let ExprKind::Con(c) = &x.kind {
            if let Some(Sym::Ty(tid)) = self.resolve(c, true) {
                if let Some(cd) = self.class_defs.get(&tid).cloned() {
                    let member = self.modules.get(&cd.module).and_then(|m| m.values.get(&name.name)).copied();
                    if let Some(acc) = self.assoc_defs.get(&(tid, name.name.clone())).copied() {
                        return self.assoc_without_types(tid, acc, x.span, name, span);
                    }
                    let is_member = cd.members.iter().any(|m| !matches!(m, ast::ClassMember::Type { .. }) && m.name().name == name.name);
                    return match member {
                        Some(s @ Sym::Def(d)) if is_member => {
                            self.index_sym(x.span, Sym::Ty(tid));
                            self.index_sym(name.span, s);
                            self.note_reference(d, span);
                            self.name_span = span;
                            let (t, ty) = self.sym_term(cx, s, span);
                            self.insert(cx, t, ty)
                        }
                        _ => {
                            let names: Vec<String> = cd
                                .members
                                .iter()
                                .map(|m| m.name().name.clone())
                                .collect();
                            self.err(
                                Diagnostic::error("E0206", format!("class `{}` has no function or lemma `{}`", cd.name, name.name), name.span)
                                    .with_help(format!("its members are `{}`", names.join("`, `"))),
                            );
                            (Tm::Error, Val::Error)
                        }
                    };
                }
            }
        }
        if let ExprKind::Var(q) = &x.kind {
            if cx.lookup(q).is_none() {
                if let Some(m) = self.qualifier(q) {
                    return match self.resolve_qualified(&m, &name.name, cx.type_pos) {
                        Some(s) => {
                            self.index_module(x.span, &m);
                            self.index_sym(name.span, s);
                            if let Sym::Def(d) = s {
                                self.note_reference(d, span);
                            }
                            self.name_span = span;
                            let (t, ty) = self.sym_term(cx, s, span);
                            self.insert(cx, t, ty)
                        }
                        None => {
                            let mut d = Diagnostic::error(
                                "E0206",
                                format!("module `{m}` has no export named `{}`", name.name),
                                name.span,
                            );
                            if self.declares_privately(&m, &name.name) {
                                d = self.private_help(d, &self.cur, &m, &name.name);
                            }
                            self.err(d);
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
        // A class's type at an instance not found yet (`q"…".sql`, its
        // type `Template.Result Building`, #132): find the instances the
        // types known so far choose, and look again.
        if !matches!(self.force(&xty), Val::TyCon(..)) && !self.inst_reqs.is_empty() {
            self.solve_instances(false);
            self.retry_waiting(false);
        }
        match self.force(&xty) {
            Val::TyCon(tid, _) if self.g.tys[tid.0 as usize].is_record && self.sealed_from(tid).is_some() => {
                self.err(self.sealed_error(tid, "fields", name.span));
                (Tm::Error, Val::Error)
            }
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
                self.index_global(name.span, index::Target::Field(cid, idx));
                let xv = self.eval(cx, &xt);
                // Each field's type, in the context of the parameters and the
                // fields before it.
                let mut env: Vec<Val> = params.to_vec();
                let mut ftys = Vec::new();
                for (j, f) in fields.iter().enumerate() {
                    ftys.push(eval(&self.g, &Rc::new(env.clone()), &f.3));
                    env.push(crate::core::eval(
                        &self.g,
                        &Rc::new(vec![xv.clone()]),
                        &Tm::Field(Rc::new(Tm::Var(0)), cid, j),
                    ));
                }
                // Reading a field uses the whole record: at runtime, it may
                // not drop another field holding a resource (D156, E0406).
                if self.in_spec == 0 && self.in_proof == 0 && self.val_linear(&xty) {
                    let others: Vec<String> = fields
                        .iter()
                        .zip(&ftys)
                        .enumerate()
                        .filter(|(j, (f, t))| *j != idx && f.1 != Mult::Zero && self.val_linear(t))
                        .map(|(_, (f, _))| format!("`{}`", f.0))
                        .collect();
                    if !others.is_empty() {
                        self.part_reported_at(cx, &xt);
                        let tname = self.g.tys[tid.0 as usize].name.clone();
                        let cname = self.g.cons[cid.0 as usize].name.clone();
                        let all: Vec<String> =
                            fields.iter().filter(|f| f.2 == Icit::Expl).map(|f| f.0.to_string()).collect();
                        let verb = if others.len() == 1 { "holds" } else { "hold" };
                        self.err(
                            Diagnostic::error(
                                "E0406",
                                format!("reading `{}` would drop the rest of this `{tname}`, and {} {verb} a resource", name.name, others.join(", ")),
                                name.span,
                            )
                            .with_label("reading a field uses the whole record")
                            .with_help(format!(
                                "take it apart with `match` (`{cname} {} -> …`) and use {} too",
                                all.join(" "),
                                others.join(", ")
                            )),
                        );
                    }
                }
                let fty = ftys[idx].clone();
                (Tm::Field(Rc::new(xt), cid, idx), fty)
            }
            Val::Error => (Tm::Error, Val::Error),
            _ => {
                let shown = self.show_written(cx, &xty);
                let mut d = Diagnostic::error("E0207", format!("`{shown}` has no field `{}`", name.name), name.span)
                    .with_label(format!("this is a `{shown}`, not a record"));
                // A local variable hiding an imported module of the same name.
                if let ExprKind::Var(q) = &x.kind {
                    if let Some(m) = self.qualifier(q).filter(|_| cx.lookup(q).is_some()) {
                        d = d.with_help(format!(
                            "the variable `{q}` hides the module `{m}` here; give the variable another name"
                        ));
                    }
                }
                self.err(d);
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
                        self.let_var(cx, &name, pat.span, rhs, Mult::Many, rest, result, expected, tail)
                    }
                    _ => {
                        let arms = vec![(pat.clone(), None, ArmBody::Rest(rest, result))];
                        self.elab_match(cx, rhs, arms, Some(expected), tail, pat.span).0
                    }
                }
            }
            Stmt::GhostLet(x, rhs) => self.let_var(cx, &x.name, x.span, rhs, Mult::Zero, rest, result, expected, tail),
            Stmt::HaveType(x, ty) => {
                let saved = cx.facts.len();
                self.have_type(cx, x, ty);
                let t = self.block_from(cx, rest, result, expected, tail);
                cx.facts.truncate(saved);
                t
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

        }
    }

    /// `let name = rhs` and the rest of the block. `declared`: `Many`, or
    /// `Zero` for a type bound `ghost` (`Stmt::GhostLet`); a value whose
    /// type is a resource makes a `Many` one `own` (D39).
    #[allow(clippy::too_many_arguments)]
    fn let_var(
        &mut self,
        cx: &mut Cx,
        name: &str,
        span: Span,
        rhs: &Expr,
        declared: Mult,
        rest: &[Stmt],
        result: &Expr,
        expected: &Val,
        tail: bool,
    ) -> Tm {
        let erased = declared == Mult::Zero;
        self.in_erased += erased as usize;
        let (t, ty) = self.infer(cx, rhs);
        self.in_erased -= erased as usize;
        let ty = self.reduce_type(&ty);
        if name == "_" && self.val_linear(&ty) {
            self.report_dropped(cx, &ty, span);
        }
        let mult = self.named_mult(cx, name, &ty, span, declared);
        let v = self.eval(cx, &t);
        let tyt = quote(&self.g, cx.lvl(), &ty);
        let l = cx.define_by(name, ty, v, mult, t.clone());
        if name != "_" {
            self.bound_at(cx, l, span);
        }
        // `let x = y` keeps y's structural information.
        if let ExprKind::Var(src) = &rhs.kind {
            let found = cx.locals.iter().take(l).rposition(|x| x.name.as_ref() == src.as_str());
            if let Some(sl) = found {
                cx.locals[l].sub = cx.locals[sl].sub;
                cx.locals[l].sub_cond = cx.locals[sl].sub_cond;
            }
        }
        let body = self.block_from(cx, rest, result, expected, tail);
        cx.pop();
        let nm = if name != "_" { self.binder_name(name, span) } else { Rc::from("_") };
        Tm::Let(nm, mult, Rc::new(tyt), Rc::new(t), Rc::new(body))
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
        let mut ok_args: Vec<Val> = payload.to_vec();
        ok_args.push(Val::var(l));
        cx.assume(Self::prim_val(Prim::Eq, vec![it_val, Val::Con(ok_con, ok_args.into())]));
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
                let mut args = payload.to_vec();
                args.push(Val::var(l));
                cx.assume(Self::prim_val(Prim::Eq, vec![it_val, Val::Con(err_con, args.into())]));
                let v = self.eval(cx, &err_body);
                self.oblige_posts_at(cx, v, span);
                cx.pop();
            } else {
                cx.assume(Self::prim_val(Prim::Eq, vec![it_val, Val::Con(err_con, vec![payload[0].clone()].into())]));
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
        cx.define_by(&name, ty, v, mult, t.clone());
        let body = match &pat.kind {
            ast::PatKind::Var(_) | ast::PatKind::Wild => self.block_from(cx, rest, result, expected, tail),
            _ => {
                let scrut = mk(ExprKind::Var(name.clone()), pat.span);
                let arms = vec![(pat.clone(), None, ArmBody::Rest(rest, result))];
                self.elab_match(cx, &scrut, arms, Some(expected), tail, pat.span).0
            }
        };
        cx.pop();
        let nm = match &pat.kind {
            ast::PatKind::Var(_) => self.binder_name(&name, pat.span),
            _ => Rc::from(name.as_str()),
        };
        Tm::Let(nm, mult, Rc::new(tyt), Rc::new(t), Rc::new(body))
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
        self.oblige_distinct_cowns(cx, w, &cowns, &tys);
        let start = cx.lvl();
        // The contents' refinements (a cown invariant, §8.5): facts on entry,
        // obligations on every value the body hands back.
        let many = tys.len() > 1;
        let invs: Vec<CownInv> = tys.iter().enumerate().filter_map(|(k, ty)| self.cown_inv(cx, ty, many.then_some((k, k + 1 == tys.len())))).collect();
        for ((n, _), ty) in w.binds.iter().zip(&tys) {
            let l = cx.bind(&n.name, ty.clone(), Mult::Many);
            self.bound_at(cx, l, n.span);
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
        let expected = if tys.len() == 1 { tys[0].clone() } else { Val::TupleTy(tys.clone().into()) };
        let body = self.check_block(cx, &w.body, &expected, true);
        self.post_target = None;
        cx.truncate(start);
        let mut lam = body;
        for (n, _) in w.binds.iter().rev() {
            lam = Tm::Lam(Rc::from(n.name.as_str()), Mult::Many, Icit::Expl, Rc::new(lam));
        }
        Tm::PrimApp(Prim::When, vec![st, Tm::Tuple(cowns), lam])
    }
}

fn pvar(n: &str, span: Span) -> ast::Pattern {
    ast::Pattern { kind: ast::PatKind::Var(n.to_string()), span }
}

/// Does `t`, a term over `total` binders (de Bruijn indices), mention a
/// binder at level `from` or later? `depth` counts binders inside `t`.
fn mentions_level_from(t: &Tm, total: usize, from: usize, depth: usize) -> bool {
    match t {
        Tm::Var(i) => *i >= depth && total + depth - 1 - i >= from,
        _ => t.any_sub(|x, n| mentions_level_from(x, total, from, depth + n)),
    }
}

/// The first `forall` in `e` that isn't positive (under `and`, `or`, after
/// `implies`, or in another `forall`'s conclusion), if any (D137).
pub fn negative_forall(e: &Expr, positive: bool) -> Option<Span> {
    match &e.kind {
        ExprKind::Forall(_, cs) => {
            if !positive {
                return Some(e.span);
            }
            cs.iter().find_map(|c| match c {
                Constraint::Pred(p) | Constraint::Named(_, p) => negative_forall(p, true),
                Constraint::Typed { ty, .. } => negative_forall(ty, false),
            })
        }
        ExprKind::Binary(Op::And | Op::Or, a, b) => negative_forall(a, positive).or_else(|| negative_forall(b, positive)),
        ExprKind::Binary(Op::Implies, a, b) => negative_forall(a, false).or_else(|| negative_forall(b, positive)),
        ExprKind::Var(_) | ExprKind::Con(_) | ExprKind::Lit(_) | ExprKind::Unit => None,
        _ => any_forall(e),
    }
}

fn any_forall(e: &Expr) -> Option<Span> {
    let mut found = None;
    fn go(e: &Expr, found: &mut Option<Span>) {
        if found.is_some() {
            return;
        }
        match &e.kind {
            ExprKind::Forall(..) => *found = Some(e.span),
            ExprKind::Tuple(xs) | ExprKind::List(xs) | ExprKind::Par(xs) => xs.iter().for_each(|x| go(x, found)),
            ExprKind::App(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Arrow(a, b) | ExprKind::Index(a, b) => {
                go(a, found);
                go(b, found);
            }
            ExprKind::Neg(a) | ExprKind::Field(a, _) | ExprKind::Try(a) | ExprKind::Lambda(_, a) => go(a, found),
            ExprKind::If(a, b, c) => {
                go(a, found);
                go(b, found);
                go(c, found);
            }
            ExprKind::Match(s, arms) => {
                go(s, found);
                arms.iter().for_each(|a| go(&a.body, found));
            }
            ExprKind::Template(t, ps) => {
                go(t, found);
                ps.iter().flat_map(|p| p.exprs()).for_each(|x| go(x, found));
            }
            _ => {}
        }
    }
    go(e, &mut found);
    found
}

/// A value deciding a type parameter together with others (`join_args`):
/// its parameter's type `dom`, the type `own` it was checked against, with
/// its own unknowns for the parameters (`metas`: parameter, own), and the
/// value.
pub struct JoinArg {
    pub span: Span,
    pub dom: Val,
    pub own: Val,
    pub tm: Tm,
    pub metas: Vec<(MetaId, MetaId)>,
}

/// The unknowns `t` mentions.
fn metas_in(t: &Tm, out: &mut Vec<MetaId>) {
    if let Tm::Meta(m) = t {
        if !out.contains(m) {
            out.push(*m);
        }
    }
    t.any_sub(|s, _| {
        metas_in(s, out);
        false
    });
}

/// Does `t` mention a function type?
fn has_pi(t: &Tm) -> bool {
    matches!(t, Tm::Pi(..)) || t.any_sub(|s, _| has_pi(s))
}

/// The first application of the unknown `m` in `t`, with its arguments.
fn meta_app(t: &Tm, m: MetaId) -> Option<Tm> {
    if matches!(t.head(), Tm::Meta(x) if *x == m) {
        return Some(t.clone());
    }
    let mut found = None;
    t.any_sub(|s, _| {
        found = meta_app(s, m);
        found.is_some()
    });
    found
}

/// `t` with the unknown `from` replaced by `to`.
fn rename_meta(t: &Tm, from: MetaId, to: MetaId) -> Tm {
    match t {
        Tm::Meta(x) if *x == from => Tm::Meta(to),
        _ => t.map_sub(|s, _| rename_meta(s, from, to)),
    }
}
