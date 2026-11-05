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
    binds: Vec<(String, usize)>,
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
                        let pats = match p.kind {
                            PatKind::Tuple(ps) => locals.iter().copied().zip(ps).collect(),
                            _ => vec![],
                        };
                        Row { pats, binds: vec![], guard, body }
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
        let rows = arms
            .into_iter()
            .map(|(p, guard, body)| Row { pats: vec![(occ, p)], binds: vec![], guard, body })
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
                PatKind::Var(n) => r.binds.push((n, occ)),
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
        let start = cx.lvl();
        let mut lets = Vec::new();
        for (name, occ) in &row.binds {
            let ty = cx.locals[*occ].ty.clone();
            let v = cx.env[*occ].clone();
            let tyt = quote(&self.g, cx.lvl(), &ty);
            let t = cx.var(*occ);
            let l = cx.define(name, ty, v, Mult::Many);
            cx.locals[l].sub = cx.locals[*occ].sub;
            cx.locals[l].param = cx.locals[*occ].param;
            lets.push((name.clone(), tyt, t));
        }
        let body = match row.guard {
            None => self.arm_body(cx, row.body, expected, tail),
            Some(g) => {
                let b = self.bool_ty();
                let gt = self.check(cx, g, &b, false);
                let bt = self.arm_body(cx, row.body, expected, tail);
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
                self.if_tm(gt, bt, et)
            }
        };
        cx.truncate(start);
        let mut t = body;
        for (n, tyt, v) in lets.into_iter().rev() {
            t = Tm::Let(Rc::from(n.as_str()), Mult::Many, Rc::new(tyt), Rc::new(v), Rc::new(t));
        }
        t
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
            let body = if rs.is_empty() { Tm::Error } else { self.compile(cx, rs, expected, tail) };
            branches.push((lit.clone(), body));
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
                Some(Sym::Con(c)) => Some((c, Some(args.clone()))),
                _ => {
                    unknown(self, name);
                    None
                }
            },
            PatKind::Record(name, _) => match self.resolve(&name.name, false) {
                Some(Sym::Con(c)) => Some((c, None)),
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
            let body = if rs.is_empty() {
                let w = self.render_path();
                self.note_missing(format!("`{w}`"));
                Tm::Error
            } else {
                self.compile(cx, rs, expected, tail)
            };
            self.pm.frames.pop();
            cx.truncate(start);
            branches.push((c, fields.len(), body));
        }
        Tm::Case(Rc::new(scrut), Rc::new(CaseTm { branches, lits: vec![], default: None }))
    }
}
