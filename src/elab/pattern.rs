//! `match`: compile nested patterns to case trees and check exhaustiveness (D4).
//!
//! A classic clause-matrix compiler. Each row is a list of (occurrence, pattern)
//! pairs; occurrences are locals. Arm bodies are elaborated at the leaves (a
//! body can be reached from several leaves; diagnostics are de-duplicated).

use super::expr::ArmBody;
use super::*;
use crate::syntax::ast::{Expr, ExprKind, PatKind, Pattern};

#[derive(Clone)]
pub struct Row<'a> {
    pats: Vec<(usize, Pattern)>,
    /// The arm's whole pattern, for errors about it.
    span: Span,
    /// Names bound, the occurrence each names, and where it is written.
    binds: Vec<(String, usize, Span)>,
    guard: Option<&'a Expr>,
    body: ArmBody<'a>,
}

enum Column {
    Tuple,
    Con,
    Lit,
}

/// How a value on the current decision path was taken apart.
#[derive(Clone, Debug)]
enum Frame {
    Ctor(ConId, Vec<usize>),
    Tuple(Vec<usize>),
}

/// Exhaustiveness bookkeeping for one `match`.
#[derive(Default, Debug)]
pub struct PatState {
    /// The occurrences being matched (several for `match (a, b)` on locals).
    roots: Vec<usize>,
    /// Constructors chosen so far on the current path, by occurrence.
    frames: Vec<(usize, Frame)>,
    /// Uncovered values, as patterns.
    missing: Vec<String>,
    /// A pattern was ill-formed; don't also report missing cases.
    bad: bool,
    /// Arms already reported for dropping a resource (each arm once).
    dropped: Vec<Span>,
}

impl Elab {
    fn pat_err(&mut self, d: Diagnostic) {
        self.pm.bad = true;
        self.err(d);
    }

    /// Render occurrence `o` as a pattern, from the constructors chosen on the current path.
    fn render_occ(&self, o: usize) -> String {
        let Some((_, f)) = self.pm.frames.iter().rev().find(|(x, _)| *x == o) else { return "_".into() };
        let wrap = |s: String| if s.contains(' ') && !s.starts_with('(') { format!("({s})") } else { s };
        match f {
            Frame::Tuple(cs) => format!("({})", cs.iter().map(|c| self.render_occ(*c)).collect::<Vec<_>>().join(", ")),
            Frame::Ctor(c, fs) => {
                let wk = &self.g.well_known;
                if Some(*c) == wk.nil {
                    return "[]".into();
                }
                if Some(*c) == wk.cons && fs.len() == 2 {
                    return format!("{} :: {}", wrap(self.render_occ(fs[0])), self.render_occ(fs[1]));
                }
                let mut s = self.g.cons[c.0 as usize].name.to_string();
                for f in fs {
                    s.push(' ');
                    s += &wrap(self.render_occ(*f));
                }
                s
            }
        }
    }

    fn render_path(&self) -> String {
        match self.pm.roots.as_slice() {
            [r] => self.render_occ(*r),
            rs => format!("({})", rs.iter().map(|r| self.render_occ(*r)).collect::<Vec<_>>().join(", ")),
        }
    }

    fn note_missing(&mut self, item: String) {
        if !self.pm.missing.contains(&item) {
            self.pm.missing.push(item);
        }
    }

    /// Report the uncovered values of the `match` that just finished, as one error.
    fn report_missing(&mut self, span: Span) {
        let missing = std::mem::take(&mut self.pm.missing);
        if missing.is_empty() || self.pm.bad {
            return;
        }
        let shown: Vec<String> = missing.iter().take(3).cloned().collect();
        let mut list = match shown.len() {
            1 => shown[0].clone(),
            2 => format!("{} or {}", shown[0], shown[1]),
            _ => format!("{}, {} or {}", shown[0], shown[1], shown[2]),
        };
        if missing.len() > 3 {
            list = format!("{}, {}, {} and {} more", shown[0], shown[1], shown[2], missing.len() - 3);
        }
        let help = match missing.as_slice() {
            [one] if one.starts_with('`') && !one.contains(" when ") && !one.contains(" for ") => {
                format!("add an arm `{} -> …`, or a catch-all `_ -> …`", one.trim_matches('`'))
            }
            [_] => "add an arm for it, or a catch-all `_ -> …`".to_string(),
            _ => "add arms for these, or a catch-all `_ -> …`".to_string(),
        };
        self.err(
            Diagnostic::error("E0240", format!("this `match` does not cover {list}"), span)
                .with_label("not exhaustive")
                .with_help(help),
        );
    }

    pub fn elab_match<'a>(
        &mut self,
        cx: &mut Cx,
        scrut: &Expr,
        arms: Vec<(Pattern, Option<&'a Expr>, ArmBody<'a>)>,
        expected: Option<&Val>,
        tail: bool,
        span: Span,
    ) -> (Tm, Val) {
        let saved_span = std::mem::replace(&mut self.match_span, span);
        let saved_pm = std::mem::take(&mut self.pm);
        let r = self.elab_match_inner(cx, scrut, arms, expected, tail);
        self.report_missing(span);
        self.pm = saved_pm;
        self.match_span = saved_span;
        r
    }

    fn elab_match_inner<'a>(
        &mut self,
        cx: &mut Cx,
        scrut: &Expr,
        arms: Vec<(Pattern, Option<&'a Expr>, ArmBody<'a>)>,
        expected: Option<&Val>,
        tail: bool,
    ) -> (Tm, Val) {
        let expected = match expected {
            Some(e) => e.clone(),
            None => self.fresh_meta_val(cx),
        };
        let start = cx.lvl();
        // `match (a, b)` on local variables matches the variables directly, so
        // structural recursion on either of them is still recognised.
        if let ExprKind::Tuple(items) = &scrut.kind {
            let locals: Option<Vec<usize>> = items
                .iter()
                .map(|it| match &it.kind {
                    ExprKind::Var(n) => cx.lookup(n),
                    _ => None,
                })
                .collect();
            let all_tuple_pats = arms.iter().all(|(p, _, _)| match &p.kind {
                PatKind::Tuple(ps) => ps.len() == items.len(),
                PatKind::Wild => true,
                _ => false,
            });
            if let (Some(locals), true) = (locals, all_tuple_pats) {
                let rows = arms
                    .into_iter()
                    .map(|(p, guard, body)| {
                        let p_span = p.span;
                        let pats = match p.kind {
                            PatKind::Tuple(ps) => locals.iter().copied().zip(ps).collect(),
                            _ => vec![],
                        };
                        Row { pats, span: p_span, binds: vec![], guard, body }
                    })
                    .collect();
                self.pm.roots = locals;
                let t = self.compile(cx, rows, &expected, tail);
                return (t, expected);
            }
        }
        let (occ, wrap) = match &scrut.kind {
            ExprKind::Var(n) if cx.lookup(n).is_some() => (cx.lookup(n).unwrap(), None),
            _ => {
                let (st, sty) = self.infer(cx, scrut);
                let v = self.eval(cx, &st);
                let tyt = quote(&self.g, cx.lvl(), &sty);
                let l = cx.define("$s", sty, v, Mult::Many);
                (l, Some((st, tyt)))
            }
        };
        // Completing a pattern (D142): the type matched.
        if arms.iter().any(|(p, _, _)| matches!(&p.kind, PatKind::Var(n) if Self::is_cursor(n))) {
            let ty = cx.locals[occ].ty.clone();
            self.note_scrutinee(cx, &ty);
        }
        let rows = arms
            .into_iter()
            .map(|(p, guard, body)| Row { span: p.span, pats: vec![(occ, p)], binds: vec![], guard, body })
            .collect();
        self.pm.roots = vec![occ];
        let t = self.compile(cx, rows, &expected, tail);
        cx.truncate(start);
        let t = match wrap {
            Some((st, tyt)) => Tm::Let(Rc::from("$s"), Mult::Many, Rc::new(tyt), Rc::new(st), Rc::new(t)),
            None => t,
        };
        (t, expected)
    }

    fn expand_or<'a>(row: Row<'a>) -> Vec<Row<'a>> {
        for (i, (occ, p)) in row.pats.iter().enumerate() {
            if let PatKind::Or(alts) = &p.kind {
                let mut out = Vec::new();
                for a in alts {
                    let mut r = row.clone();
                    r.pats[i] = (*occ, a.clone());
                    out.extend(Self::expand_or(r));
                }
                return out;
            }
        }
        vec![row]
    }

    fn simplify(row: Row) -> Row {
        let mut r = row;
        let mut pats = Vec::new();
        for (occ, p) in r.pats.drain(..) {
            match p.kind {
                PatKind::Wild | PatKind::Unit => {}
                PatKind::Var(n) => r.binds.push((n, occ, p.span)),
                _ => pats.push((occ, p)),
            }
        }
        r.pats = pats;
        r
    }

    fn compile(&mut self, cx: &mut Cx, rows: Vec<Row>, expected: &Val, tail: bool) -> Tm {
        let rows: Vec<Row> = rows.into_iter().flat_map(Self::expand_or).map(Self::simplify).collect();
        if rows.is_empty() {
            return Tm::Error;
        }
        if rows[0].pats.is_empty() {
            return self.leaf(cx, rows, expected, tail);
        }
        let (occ, pat) = rows[0].pats[0].clone();
        let col = match &pat.kind {
            PatKind::Tuple(_) => Column::Tuple,
            PatKind::Lit(_) | PatKind::Neg(_) => Column::Lit,
            _ => Column::Con,
        };
        match col {
            Column::Tuple => self.compile_tuple(cx, rows, occ, &pat, expected, tail),
            Column::Lit => self.compile_lit(cx, rows, occ, expected, tail),
            Column::Con => self.compile_con(cx, rows, occ, &pat, expected, tail),
        }
    }

    fn leaf(&mut self, cx: &mut Cx, rows: Vec<Row>, expected: &Val, tail: bool) -> Tm {
        let row = rows[0].clone();
        self.check_dropped(cx, &row);
        let start = cx.lvl();
        let mut lets = Vec::new();
        for (name, occ, at) in &row.binds {
            let ty = cx.locals[*occ].ty.clone();
            let v = cx.env[*occ].clone();
            let tyt = quote(&self.g, cx.lvl(), &ty);
            let t = cx.var(*occ);
            let mult = self.named_mult(cx, name, &ty, *at, Mult::Many);
            let l = cx.define(name, ty, v, mult);
            cx.locals[l].sub = cx.locals[*occ].sub;
            cx.locals[l].param = cx.locals[*occ].param;
            self.bound_at(cx, l, *at);
            lets.push((name.clone(), mult, tyt, t));
        }
        let body = match row.guard {
            None => self.arm_body(cx, row.body, expected, tail),
            Some(g) => {
                let b = self.bool_ty();
                let gt = self.check(cx, g, &b, false);
                let gv = self.eval(cx, &gt);
                let saved = cx.facts.len();
                cx.assume(self.is_bool(gv.clone(), true));
                let bt = self.arm_body(cx, row.body, expected, tail);
                cx.facts.truncate(saved);
                cx.assume(self.is_bool(gv, false));
                let rest: Vec<Row> = rows[1..].to_vec();
                let et = if rest.is_empty() {
                    let w = self.render_path();
                    self.note_missing(if w == "_" {
                        "the case where the guard is false".to_string()
                    } else {
                        format!("`{w}` when the guard is false")
                    });
                    Tm::Error
                } else {
                    self.compile(cx, rest, expected, tail)
                };
                cx.facts.truncate(saved);
                self.if_tm(gt, bt, et)
            }
        };
        cx.truncate(start);
        let mut t = body;
        for (n, mult, tyt, v) in lets.into_iter().rev() {
            t = Tm::Let(Rc::from(n.as_str()), mult, Rc::new(tyt), Rc::new(v), Rc::new(t));
        }
        t
    }

    /// E0404: at a leaf, every resource reached by the match must be taken
    /// apart further or bound to a name.
    fn check_dropped(&mut self, cx: &Cx, row: &Row) {
        let mut occs: Vec<usize> = self.pm.roots.iter().copied().filter(|r| cx.locals[*r].name.starts_with('$')).collect();
        for (_, f) in &self.pm.frames {
            match f {
                Frame::Ctor(_, fs) | Frame::Tuple(fs) => occs.extend(fs.iter().copied()),
            }
        }
        // A part of a value bound whole (`other` in a later arm) isn't dropped.
        let parent = |o: usize| {
            self.pm.frames.iter().find_map(|(p, f)| match f {
                Frame::Ctor(_, fs) | Frame::Tuple(fs) => fs.contains(&o).then_some(*p),
            })
        };
        let bound = |o: usize| row.binds.iter().any(|(_, x, _)| *x == o);
        let within_bound = |mut o: usize| loop {
            if bound(o) {
                return true;
            }
            match parent(o) {
                Some(p) => o = p,
                None => return false,
            }
        };
        for o in occs {
            let taken_apart = self.pm.frames.iter().any(|(x, _)| *x == o);
            if !taken_apart && !within_bound(o) && o < cx.locals.len() {
                let ty = cx.locals[o].ty.clone();
                if self.val_linear(&ty) {
                    if !self.pm.dropped.contains(&row.span) {
                        self.pm.dropped.push(row.span);
                        self.report_dropped(cx, &ty, row.span);
                    }
                    return;
                }
            }
        }
    }

    fn compile_tuple(
        &mut self,
        cx: &mut Cx,
        rows: Vec<Row>,
        occ: usize,
        pat: &Pattern,
        expected: &Val,
        tail: bool,
    ) -> Tm {
        let PatKind::Tuple(ps) = &pat.kind else { unreachable!() };
        let n = ps.len();
        let ty = self.force(&cx.locals[occ].ty);
        let comps_ty = match ty {
            Val::TupleTy(ts) if ts.len() == n => ts,
            other => {
                // The occurrence's type can't depend on the occurrence itself.
                let mut outer = cx.clone();
                outer.truncate(occ);
                let metas: Vec<Val> = (0..n).map(|_| self.fresh_meta_val(&outer)).collect();
                let want = Val::TupleTy(metas.clone());
                if !self.unify_at(cx, &other, &want, pat.span, "this pattern") {
                    return Tm::Error;
                }
                metas
            }
        };
        let start = cx.lvl();
        let mut lets = Vec::new();
        let mut comps = Vec::new();
        for (i, cty) in comps_ty.into_iter().enumerate() {
            let tm = Tm::Proj(Rc::new(cx.var(occ)), i);
            let v = self.eval(cx, &tm);
            let tyt = quote(&self.g, cx.lvl(), &cty);
            let l = cx.define(&format!("$c{i}"), cty, v, Mult::Many);
            cx.locals[l].sub = cx.locals[occ].sub;
            comps.push(l);
            lets.push((format!("$c{i}"), tyt, tm));
        }
        let mut new_rows = Vec::new();
        for mut r in rows {
            if let Some(i) = r.pats.iter().position(|(o, _)| *o == occ) {
                let (_, p) = r.pats.remove(i);
                match p.kind {
                    PatKind::Tuple(qs) if qs.len() == n => {
                        let mut extra: Vec<(usize, Pattern)> = comps.iter().copied().zip(qs).collect();
                        extra.append(&mut r.pats);
                        r.pats = extra;
                    }
                    _ => {
                        self.pat_err(Diagnostic::error(
                            "E0246",
                            format!("expected a pattern for a {n}-tuple"),
                            p.span,
                        ));
                        continue;
                    }
                }
            }
            new_rows.push(r);
        }
        self.pm.frames.push((occ, Frame::Tuple(comps.clone())));
        let body = self.compile(cx, new_rows, expected, tail);
        self.pm.frames.pop();
        cx.truncate(start);
        let mut t = body;
        for (name, tyt, v) in lets.into_iter().rev() {
            t = Tm::Let(Rc::from(name.as_str()), Mult::Many, Rc::new(tyt), Rc::new(v), Rc::new(t));
        }
        t
    }

    fn lit_of(&mut self, p: &Pattern) -> Option<(Lit, Val)> {
        Some(match &p.kind {
            PatKind::Lit(ast::Lit::Int(s)) => {
                let n = self.number(s, p.span);
                (Lit::Num(n), Val::Error)
            }
            PatKind::Neg(s) => {
                let n = self.number(s, p.span);
                (Lit::Num(-n), self.int())
            }
            PatKind::Lit(ast::Lit::Byte(b)) => (Lit::Num(*b as i128), self.nat()),
            PatKind::Lit(ast::Lit::Char(c)) => (Lit::Num(*c as i128), self.nat()),
            PatKind::Lit(ast::Lit::Str(s)) => (Lit::Str(Rc::from(s.as_str())), self.string()),
            PatKind::Lit(ast::Lit::Bytes(b)) => (Lit::Bytes(Rc::from(b.as_slice())), self.bytes()),
            _ => return None,
        })
    }

    fn compile_lit(&mut self, cx: &mut Cx, rows: Vec<Row>, occ: usize, expected: &Val, tail: bool) -> Tm {
        let occ_ty = cx.locals[occ].ty.clone();
        let mut lits: Vec<Lit> = Vec::new();
        for r in &rows {
            if let Some((_, p)) = r.pats.iter().find(|(o, _)| *o == occ) {
                match self.lit_of(p) {
                    Some((l, ty)) => {
                        let ty = match ty {
                            Val::Error => {
                                // A plain number: Nat or Int, whichever the value is.
                                match self.force(&occ_ty) {
                                    Val::TyCon(id, _) if Some(id) == self.g.well_known.int => self.int(),
                                    _ => self.nat(),
                                }
                            }
                            t => t,
                        };
                        self.unify_at(cx, &occ_ty, &ty, p.span, "this pattern");
                        if !lits.contains(&l) {
                            lits.push(l);
                        }
                    }
                    None => {
                        self.pat_err(Diagnostic::error(
                            "E0245",
                            "this pattern doesn't match the type of the value: the other arms match literals",
                            p.span,
                        ));
                    }
                }
            }
        }
        let mut branches = Vec::new();
        for lit in &lits {
            let mut rs = Vec::new();
            for r in &rows {
                let mut r = r.clone();
                match r.pats.iter().position(|(o, _)| *o == occ) {
                    Some(i) => {
                        let same = self.lit_of(&r.pats[i].1).map(|(l, _)| l == *lit).unwrap_or(false);
                        if same {
                            r.pats.remove(i);
                            rs.push(r);
                        }
                    }
                    None => rs.push(r),
                }
            }
            let saved = cx.facts.len();
            let occ_val = cx.env[occ].clone();
            cx.assume(Self::prim_val(Prim::Eq, vec![occ_val, Val::Lit(lit.clone())]));
            let body = if rs.is_empty() { Tm::Error } else { self.compile(cx, rs, expected, tail) };
            cx.facts.truncate(saved);
            branches.push((lit.clone(), body));
        }
        let saved = cx.facts.len();
        for lit in &lits {
            let occ_val = cx.env[occ].clone();
            cx.assume(Self::prim_val(Prim::Ne, vec![occ_val, Val::Lit(lit.clone())]));
        }
        let defaults: Vec<Row> = rows.iter().filter(|r| !r.pats.iter().any(|(o, _)| *o == occ)).cloned().collect();
        let default = if defaults.is_empty() {
            let w = self.render_path();
            let tyname = self.show_val(cx, &occ_ty);
            self.note_missing(if w == "_" {
                format!("every other `{tyname}`")
            } else {
                format!("`{w}` for other values of that `{tyname}`")
            });
            Tm::Error
        } else {
            self.compile(cx, defaults, expected, tail)
        };
        cx.facts.truncate(saved);
        Tm::Case(Rc::new(cx.var(occ)), Rc::new(CaseTm { branches: vec![], lits: branches, default: Some(default) }))
    }

    /// The constructor a pattern names, and its sub-patterns (None for record patterns).
    fn pat_ctor(&mut self, p: &Pattern, hint: Option<TyId>) -> Option<(ConId, Option<Vec<Pattern>>)> {
        let wk = self.g.well_known.clone();
        let unknown = |this: &mut Self, name: &ast::Ident| {
            let mut d = Diagnostic::error("E0244", format!("unknown constructor `{}`", name.name), name.span);
            if let Some(t) = hint {
                let ti = &this.g.tys[t.0 as usize];
                let names: Vec<String> = ti.ctors.iter().map(|c| format!("`{}`", this.g.cons[c.0 as usize].name)).collect();
                d = d.with_help(format!("the constructors of `{}` are {}", ti.name, names.join(", ")));
            }
            this.pat_err(d);
        };
        match &p.kind {
            PatKind::Con(name, args) => match self.resolve(&name.name, false) {
                Some(Sym::Con(c)) => {
                    self.index_global(name.span, index::Target::Con(c));
                    Some((c, Some(args.clone())))
                }
                _ => {
                    unknown(self, name);
                    None
                }
            },
            PatKind::Record(name, _) => match self.resolve(&name.name, false) {
                Some(Sym::Con(c)) => {
                    self.index_global(name.span, index::Target::Con(c));
                    Some((c, None))
                }
                _ => {
                    unknown(self, name);
                    None
                }
            },
            PatKind::List(items) => {
                if items.is_empty() {
                    Some((wk.nil?, Some(vec![])))
                } else {
                    let rest = Pattern { kind: PatKind::List(items[1..].to_vec()), span: p.span };
                    Some((wk.cons?, Some(vec![items[0].clone(), rest])))
                }
            }
            PatKind::Cons(h, t) => Some((wk.cons?, Some(vec![(**h).clone(), (**t).clone()]))),
            _ => None,
        }
    }

    fn compile_con(&mut self, cx: &mut Cx, rows: Vec<Row>, occ: usize, pat: &Pattern, expected: &Val, tail: bool) -> Tm {
        let occ_ty = self.force(&cx.locals[occ].ty);
        let hint = match &occ_ty {
            Val::TyCon(t, _) => Some(*t),
            _ => None,
        };
        let Some((c0, _)) = self.pat_ctor(pat, hint) else { return Tm::Error };
        let tid = self.g.cons[c0.0 as usize].ty;
        let params = match occ_ty {
            Val::TyCon(t, ps) if t == tid => ps,
            Val::Error => return Tm::Error,
            other => {
                let n = self.g.arity_ty(tid);
                let mut outer = cx.clone();
                outer.truncate(occ);
                let metas: Vec<Val> = (0..n).map(|_| self.fresh_meta_val(&outer)).collect();
                let want = Val::TyCon(tid, metas.clone());
                if unify(&self.g, cx.lvl(), &other, &want).is_err() {
                    let shown = self.show_val(cx, &other);
                    let cname = self.g.cons[c0.0 as usize].name.clone();
                    let tname = self.g.tys[tid.0 as usize].name.clone();
                    self.pat_err(
                        Diagnostic::error(
                            "E0241",
                            format!("`{cname}` is a constructor of `{tname}`, but the value being matched has type `{shown}`"),
                            pat.span,
                        )
                        .with_label(format!("expected a `{shown}` pattern")),
                    );
                    return Tm::Error;
                }
                metas
            }
        };
        let scrut = cx.var(occ);
        let occ_static = self.local_static(cx, occ);
        let ctors = self.g.tys[tid.0 as usize].ctors.clone();
        let mut branches = Vec::new();
        for c in ctors {
            let start = cx.lvl();
            let fields = self.g.cons[c.0 as usize].fields.clone();
            let mut env: Vec<Val> = params.clone();
            let mut lvls = Vec::new();
            let sub = cx.locals[occ].sub.or(cx.locals[occ].param);
            for (n, m, _, fty) in &fields {
                let ty = eval(&self.g, &Rc::new(env.clone()), fty);
                let mult = if *m == Mult::Zero { Mult::Zero } else { Mult::Many };
                let l = cx.bind(&format!("${n}"), ty, mult);
                cx.locals[l].sub = sub;
                cx.locals[l].comptime = occ_static;
                env.push(Val::var(l));
                lvls.push(l);
            }
            let explicit: Vec<usize> =
                fields.iter().zip(&lvls).filter(|(f, _)| f.2 == Icit::Expl).map(|(_, l)| *l).collect();
            let mut rs = Vec::new();
            for r in &rows {
                let mut r = r.clone();
                let Some(i) = r.pats.iter().position(|(o, _)| *o == occ) else {
                    rs.push(r);
                    continue;
                };
                let p = r.pats[i].1.clone();
                let Some((pc, args)) = self.pat_ctor(&p, Some(tid)) else { continue };
                if self.g.cons[pc.0 as usize].ty != tid {
                    let shown = self.g.tys[tid.0 as usize].name.clone();
                    let cname = self.g.cons[pc.0 as usize].name.clone();
                    self.pat_err(Diagnostic::error(
                        "E0241",
                        format!("`{cname}` is not a constructor of `{shown}`"),
                        p.span,
                    ));
                    continue;
                }
                if pc != c {
                    continue;
                }
                r.pats.remove(i);
                let mut sub_pats: Vec<(usize, Pattern)> = match (args, &p.kind) {
                    (Some(args), _) => {
                        if args.len() != explicit.len() {
                            let cname = self.g.cons[c.0 as usize].name.clone();
                            self.pat_err(Diagnostic::error(
                                "E0242",
                                format!(
                                    "`{cname}` has {} field{}, but this pattern gives {}",
                                    explicit.len(),
                                    if explicit.len() == 1 { "" } else { "s" },
                                    args.len()
                                ),
                                p.span,
                            ));
                            continue;
                        }
                        explicit.iter().copied().zip(args).collect()
                    }
                    (None, PatKind::Record(_, fps)) => {
                        let mut v = Vec::new();
                        for (fname, fp) in fps {
                            match fields.iter().position(|f| f.0.as_ref() == fname.name) {
                                Some(k) => v.push((lvls[k], fp.clone())),
                                None => {
                                    let cname = self.g.cons[c.0 as usize].name.clone();
                                    self.pat_err(Diagnostic::error(
                                        "E0243",
                                        format!("`{cname}` has no field `{}`", fname.name),
                                        fname.span,
                                    ));
                                }
                            }
                        }
                        v
                    }
                    _ => vec![],
                };
                sub_pats.append(&mut r.pats);
                r.pats = sub_pats;
                rs.push(r);
            }
            self.pm.frames.push((occ, Frame::Ctor(c, explicit.clone())));
            // In this arm the value is this constructor, and its invariants hold (§7.1).
            let saved = cx.facts.len();
            let fvals: Vec<Val> = lvls.iter().map(|l| Val::var(*l)).collect();
            let mut all: Vec<Val> = params.clone();
            all.extend(fvals);
            let occ_val = cx.env[occ].clone();
            cx.assume(Self::prim_val(Prim::Eq, vec![occ_val, Val::Con(c, all.clone())]));
            for inv in self.con_invs.get(&c).cloned().unwrap_or_default() {
                let f = self.inst_pred(&inv, all.clone());
                cx.assume(f);
            }
            // Dependent matching: where the matched value is a variable, the
            // expected type sees it as this constructor (`f~format_type ps`
            // becomes `f~format_type []` in the `[]` arm).
            // Only a type that mentions the variable, and has no unknowns
            // left (an unknown abstracts over the variable itself).
            let refined = if cx.locals[occ].bound {
                let tm = quote(&self.g, cx.lvl(), expected);
                if !has_meta_tm(&tm) && mentions_var(&tm, cx.lvl() - 1 - occ) {
                    let mut env = cx.env.to_vec();
                    env[occ] = Val::Con(c, all.clone());
                    eval(&self.g, &Rc::new(env), &tm)
                } else {
                    expected.clone()
                }
            } else {
                expected.clone()
            };
            let body = if rs.is_empty() {
                let w = self.render_path();
                self.note_missing(format!("`{w}`"));
                Tm::Error
            } else {
                self.compile(cx, rs, &refined, tail)
            };
            cx.facts.truncate(saved);
            self.pm.frames.pop();
            cx.truncate(start);
            branches.push((c, fields.len(), body));
        }
        Tm::Case(Rc::new(scrut), Rc::new(CaseTm { branches, lits: vec![], default: None }))
    }
}

fn has_meta_tm(t: &Tm) -> bool {
    match t {
        Tm::Meta(_) => true,
        Tm::Pi(_, _, _, a, b) | Tm::App(a, b, ..) => has_meta_tm(a) || has_meta_tm(b),
        Tm::Lam(_, _, _, b) | Tm::Proj(b, _) | Tm::Field(b, _, _) => has_meta_tm(b),
        Tm::Let(_, _, a, b, c) => has_meta_tm(a) || has_meta_tm(b) || has_meta_tm(c),
        Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => v.iter().any(has_meta_tm),
        Tm::Case(s, c) => {
            has_meta_tm(s)
                || c.branches.iter().any(|(_, _, b)| has_meta_tm(b))
                || c.lits.iter().any(|(_, b)| has_meta_tm(b))
                || c.default.as_ref().is_some_and(has_meta_tm)
        }
        _ => false,
    }
}

/// Does `t` mention variable `i` (de Bruijn, at its top)?
fn mentions_var(t: &Tm, i: usize) -> bool {
    match t {
        Tm::Var(j) => *j == i,
        Tm::Pi(_, _, _, a, b) => mentions_var(a, i) || mentions_var(b, i + 1),
        Tm::Lam(_, _, _, b) => mentions_var(b, i + 1),
        Tm::App(a, b, ..) => mentions_var(a, i) || mentions_var(b, i),
        Tm::Proj(b, _) | Tm::Field(b, _, _) => mentions_var(b, i),
        Tm::Let(_, _, a, b, c) => mentions_var(a, i) || mentions_var(b, i) || mentions_var(c, i + 1),
        Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => {
            v.iter().any(|x| mentions_var(x, i))
        }
        Tm::Case(s, c) => {
            mentions_var(s, i)
                || c.branches.iter().any(|(_, n, b)| mentions_var(b, i + n))
                || c.lits.iter().any(|(_, b)| mentions_var(b, i))
                || c.default.as_ref().is_some_and(|b| mentions_var(b, i))
        }
        _ => false,
    }
}
