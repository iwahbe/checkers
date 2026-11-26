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
    /// The alternatives of the arm's `|` patterns this row takes.
    alts: Vec<Span>,
}

enum Column {
    Tuple,
    /// `()`: matches every value of type `()`, and only that type.
    Unit,
    Con,
    Lit,
    /// `[]` and `x :: rest` on a sequence that isn't a list: a `match` on
    /// `Seq.uncons`'s result (§9.8).
    Seq(DefId),
}

/// The names of `Option`'s constructors in the patterns a sequence pattern
/// becomes: no program can write them, so no declaration shadows them.
const SEQ_NONE: &str = "$None";
const SEQ_SOME: &str = "$Some";

/// How a value on the current decision path was taken apart.
#[derive(Clone, Debug)]
enum Frame {
    Ctor(ConId, Vec<usize>),
    Tuple(Vec<usize>),
    /// A sequence taken apart by `uncons`, its result at this occurrence.
    Seq(usize),
}

/// Exhaustiveness bookkeeping for one `match`.
#[derive(Default)]
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
    /// Cases left out, each an obligation that it can't occur (D144 e).
    uncovered: Vec<Obligation>,
    /// The arms some value reaches (the others are W021).
    reached: Vec<Span>,
    /// Each row that reached its arm's body: the arm, and the alternatives
    /// of its `|` patterns taken, in order of their spans.
    reached_rows: Vec<(Span, Vec<Span>)>,
    /// Checking rows no value reaches (`check_unreached`): there is no
    /// case left out, and the body of an arm already checked is skipped.
    unreached: bool,
    /// Arms whose bodies have been checked.
    bodies: Vec<Span>,
    /// The facts in scope before the `match`.
    facts_before: usize,
}

/// What to do about a case a binding's pattern (`let y :: _ = l`) leaves
/// out: it has no arms to add.
pub const BINDING_HELP: &str =
    "take it apart with a `match` that handles that case too, or make the facts here rule it out (a precondition, an `if`)";

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
            Frame::Seq(u) => {
                let wk = &self.g.well_known;
                let Some((_, Frame::Ctor(c, fs))) = self.pm.frames.iter().rev().find(|(x, _)| x == u) else { return "_".into() };
                if Some(*c) == wk.none {
                    return "[]".into();
                }
                let Some((_, Frame::Tuple(parts))) = fs.first().and_then(|p| self.pm.frames.iter().rev().find(|(x, _)| x == p)) else {
                    return "_ :: _".into();
                };
                format!("{} :: {}", wrap(self.render_occ(parts[0])), self.render_occ(parts[1]))
            }
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

    /// A case the arms leave out (D144 e): an obligation that it can't
    /// occur here, or in a specification (no obligations) an error.
    fn uncovered(&mut self, cx: &Cx, item: String) {
        if self.pm.unreached {
            return;
        }
        if self.in_spec > 0 || self.completing.is_some() {
            self.note_missing(item);
            return;
        }
        let f = self.false_val();
        let span = self.match_span;
        let o = self.obligation(cx, span, ObKind::Uncovered { case: item, binding: self.match_binding }, String::new(), f, None);
        self.pm.uncovered.push(o);
    }

    /// Report the uncovered values of the `match` that just finished, as one
    /// error; record the obligations for cases left out; W021 for arms no
    /// value reaches.
    fn report_missing(&mut self, span: Span, arms: &[Span]) {
        let uncovered = std::mem::take(&mut self.pm.uncovered);
        if !self.pm.bad {
            self.obligations.extend(uncovered);
            // The standard library and dependencies aren't reported (D144).
            let own = !self.stdlib_mode && self.package_of(&self.cur) == ".";
            for a in arms.iter().filter(|_| own) {
                if !self.pm.reached.contains(a) && a.start < SYNTHETIC {
                    self.err(
                        Diagnostic::warning("W021", "this arm never matches", *a)
                            .with_label("the arms above already match every value it would")
                            .with_help("remove it"),
                    );
                }
            }
        }
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
            _ if self.match_binding => BINDING_HELP.to_string(),
            [one] if one.starts_with('`') && !one.contains(" when ") && !one.contains(" for ") => {
                format!("add an arm `{} -> …`, or a catch-all `_ -> …`", one.trim_matches('`'))
            }
            [_] => "add an arm for it, or a catch-all `_ -> …`".to_string(),
            _ => "add arms for these, or a catch-all `_ -> …`".to_string(),
        };
        let what = if self.match_binding { "pattern" } else { "`match`" };
        self.err(
            Diagnostic::error("E0240", format!("this {what} does not cover {list}"), span)
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
        self.pm.facts_before = cx.facts.len();
        let arm_spans: Vec<Span> = arms.iter().map(|(p, _, _)| p.span).collect();
        let binding = arm_spans.len() == 1 && arm_spans[0] == span;
        let saved_binding = std::mem::replace(&mut self.match_binding, binding);
        let r = self.elab_match_inner(cx, scrut, arms, expected, tail);
        self.report_missing(span, &arm_spans);
        self.pm = saved_pm;
        self.match_span = saved_span;
        self.match_binding = saved_binding;
        r
    }

    /// W011: a `match` on `Seq.uncons e` whose arms sequence patterns on
    /// `e` can write (§9.8): `None` is `[]` and `Some (p, q)` is `p :: q`.
    /// Not for a `let`'s or a lambda's pattern, nor where the sequence's
    /// type isn't known yet (there `[]` and `::` would be a list's).
    fn lint_uncons_match(&mut self, scrut: &Expr, st: &Tm, sty: &Val, arms: &[(Pattern, Option<&Expr>, ArmBody<'_>)]) {
        if self.match_binding || self.stdlib_mode || self.package_of(&self.cur) != "." || scrut.span.start >= SYNTHETIC {
            return;
        }
        let ExprKind::App(_, arg) = &scrut.kind else { return };
        let Some(Sym::Def(uncons)) = self.modules.get("std.prelude").and_then(|m| m.values.get("uncons").copied()) else { return };
        if !matches!(st.head(), Tm::Def(d) if *d == uncons) {
            return;
        }
        // `Option (Elem, s)`: `s` must be known.
        let known = match self.force(sty) {
            Val::TyCon(_, args) => match args.first().map(|a| self.force(a)) {
                Some(Val::TupleTy(xs)) if xs.len() == 2 => !matches!(self.force(&xs[1]), Val::Neutral(Head::Meta(_), _) | Val::Error),
                _ => false,
            },
            _ => false,
        };
        if !known {
            return;
        }
        let Some(pats) = arms.iter().map(|(p, _, _)| self.seq_pattern_text(p)).collect::<Option<Vec<String>>>() else { return };
        // An argument's span has its parentheses, which `match` doesn't need.
        let written = self.src_text(arg.span);
        let seq = match written.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
            Some(t) if !matches!(arg.kind, ExprKind::Tuple(_) | ExprKind::Unit) => t.to_string(),
            _ => written.clone(),
        };
        let rewrites: Vec<String> = arms
            .iter()
            .zip(&pats)
            .filter_map(|((p, _, _), q)| {
                let was = self.src_text(p.span);
                (was != *q).then(|| format!("`{q}` for `{was}`"))
            })
            .collect();
        let help = if rewrites.is_empty() {
            format!("write `match {seq}`")
        } else {
            format!("write `match {seq}`, with {}", and_list(&rewrites))
        };
        self.err(
            Diagnostic::warning("W011", format!("match on `{seq}` itself, not on `Seq.uncons {written}`"), scrut.span)
                .with_label("`[]` and `x :: rest` take a sequence apart with `Seq.uncons`")
                .with_help(help),
        );
    }

    /// A pattern on `Seq.uncons`'s result written as a sequence pattern, if
    /// it can be: `None` is `[]`, `Some (p, q)` is `p :: q`.
    fn seq_pattern_text(&self, p: &Pattern) -> Option<String> {
        let wk = &self.g.well_known;
        let con = |n: &ast::Ident| match self.resolve(&n.name, false) {
            Some(Sym::Con(c)) => Some(c),
            _ => None,
        };
        match &p.kind {
            PatKind::Wild => Some("_".to_string()),
            PatKind::Con(n, args) if args.is_empty() && con(n).is_some() && con(n) == wk.none => Some("[]".to_string()),
            PatKind::Con(n, args) if args.len() == 1 && con(n).is_some() && con(n) == wk.some => match &args[0].kind {
                PatKind::Wild => Some("_ :: _".to_string()),
                PatKind::Tuple(xs) if xs.len() == 2 => {
                    let side = |q: &Pattern, left: bool| {
                        let t = self.src_text(q.span);
                        if matches!(q.kind, PatKind::Or(_)) || (left && matches!(q.kind, PatKind::Cons(..))) {
                            format!("({t})")
                        } else {
                            t
                        }
                    };
                    Some(format!("{} :: {}", side(&xs[0], true), side(&xs[1], false)))
                }
                _ => None,
            },
            PatKind::Or(alts) => alts.iter().map(|a| self.seq_pattern_text(a)).collect::<Option<Vec<_>>>().map(|v| v.join(" | ")),
            _ => None,
        }
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
                let rows: Vec<Row> = arms
                    .into_iter()
                    .map(|(p, guard, body)| {
                        let p_span = p.span;
                        let pats = match p.kind {
                            PatKind::Tuple(ps) => locals.iter().copied().zip(ps).collect(),
                            _ => vec![],
                        };
                        Row { pats, span: p_span, binds: vec![], guard, body, alts: vec![] }
                    })
                    .collect();
                self.pm.roots = locals;
                let arms: Vec<Row> = rows.clone();
                let t = self.compile(cx, rows, &expected, tail);
                self.check_unreached(cx, arms, &expected, tail);
                return (t, expected);
            }
        }
        let (occ, wrap) = match &scrut.kind {
            ExprKind::Var(n) if cx.lookup(n).is_some() => (cx.lookup(n).unwrap(), None),
            _ => {
                let (st, sty) = self.infer(cx, scrut);
                self.lint_uncons_match(scrut, &st, &sty, &arms);
                let v = self.eval(cx, &st);
                let tyt = quote(&self.g, cx.lvl(), &sty);
                let l = cx.define("$s", sty, v, Mult::Many);
                (l, Some((st, tyt)))
            }
        };
        // Completing a pattern (D142): the type matched.
        if arms.iter().any(|(p, _, _)| matches!(&p.kind, PatKind::Var(n) if Self::is_cursor(n))) {
            let ty = cx.ty_of(occ);
            self.note_scrutinee(cx, &ty);
        }
        let rows: Vec<Row> = arms
            .into_iter()
            .map(|(p, guard, body)| Row { span: p.span, pats: vec![(occ, p)], binds: vec![], guard, body, alts: vec![] })
            .collect();
        self.pm.roots = vec![occ];
        let arms: Vec<Row> = rows.clone();
        let t = self.compile(cx, rows, &expected, tail);
        self.check_unreached(cx, arms, &expected, tail);
        cx.truncate(start);
        let t = match wrap {
            Some((st, tyt)) => Tm::Let(Rc::from("$s"), Mult::Many, Rc::new(tyt), Rc::new(st), Rc::new(t)),
            None => t,
        };
        (t, expected)
    }

    /// Check the rows of `arms` that no value reached when the `match` was
    /// compiled (an arm the arms above cover, an alternative of a `|`
    /// pattern the others cover), each alone: its pattern against the type
    /// of the value matched, its guard and body against theirs, as if it
    /// were the only arm. No value reaches them, so the facts there are
    /// `False`: what they would have to prove holds.
    fn check_unreached<'a>(&mut self, cx: &mut Cx, arms: Vec<Row<'a>>, expected: &Val, tail: bool) {
        let rows: Vec<Row<'a>> = arms
            .into_iter()
            .flat_map(Self::expand_all)
            .filter(|r| {
                let mut alts = r.alts.clone();
                alts.sort_by_key(|a| a.start);
                !self.pm.reached_rows.iter().any(|(s, a)| *s == r.span && *a == alts)
            })
            .collect();
        if rows.is_empty() {
            return;
        }
        let bad = self.pm.bad;
        let facts = cx.facts.len();
        // Code no value reaches never runs: termination doesn't see its
        // calls or its uses of parameters (§5.3).
        let (calls, measure_obs, rec_calls) = (self.calls.len(), self.measure_obs.len(), self.rec_calls.len());
        let param_uses = self.param_uses.clone();
        let f = self.false_val();
        cx.assume(f);
        self.pm.unreached = true;
        for r in rows {
            self.compile(cx, vec![r], expected, tail);
        }
        self.pm.unreached = false;
        cx.facts.truncate(facts);
        self.calls.truncate(calls);
        self.measure_obs.truncate(measure_obs);
        self.rec_calls.truncate(rec_calls);
        self.param_uses = param_uses;
        // Whether the arms cover every case was decided by the `match`.
        self.pm.bad = bad;
    }

    /// Every row a row's `|` patterns make, at every depth.
    fn expand_all<'a>(row: Row<'a>) -> Vec<Row<'a>> {
        let pats: Vec<Pattern> = row.pats.iter().map(|(_, p)| p.clone()).collect();
        Self::expand_seq(&pats)
            .into_iter()
            .map(|(ps, alts)| {
                let mut r = row.clone();
                r.pats = r.pats.iter().map(|(o, _)| *o).zip(ps).collect();
                r.alts.extend(alts);
                r
            })
            .collect()
    }

    /// Each choice of alternatives in `ps`: the patterns without `|`, and
    /// the alternatives taken.
    fn expand_seq(ps: &[Pattern]) -> Vec<(Vec<Pattern>, Vec<Span>)> {
        let mut out: Vec<(Vec<Pattern>, Vec<Span>)> = vec![(vec![], vec![])];
        for p in ps {
            let mut next = Vec::new();
            for (qs, alts) in &out {
                for (q, more) in Self::expand_pat(p) {
                    let mut qs = qs.clone();
                    qs.push(q);
                    let mut alts = alts.clone();
                    alts.extend(more);
                    next.push((qs, alts));
                }
            }
            out = next;
        }
        out
    }

    fn expand_pat(p: &Pattern) -> Vec<(Pattern, Vec<Span>)> {
        let span = p.span;
        let with = |kind: PatKind| Pattern { kind, span };
        match &p.kind {
            PatKind::Or(alts) => alts
                .iter()
                .flat_map(|a| {
                    Self::expand_pat(a).into_iter().map(move |(q, mut more)| {
                        more.insert(0, a.span);
                        (q, more)
                    })
                })
                .collect(),
            PatKind::Con(n, ps) => {
                Self::expand_seq(ps).into_iter().map(|(qs, a)| (with(PatKind::Con(n.clone(), qs)), a)).collect()
            }
            PatKind::Tuple(ps) => Self::expand_seq(ps).into_iter().map(|(qs, a)| (with(PatKind::Tuple(qs)), a)).collect(),
            PatKind::List(ps) => Self::expand_seq(ps).into_iter().map(|(qs, a)| (with(PatKind::List(qs)), a)).collect(),
            PatKind::Cons(h, t) => Self::expand_seq(&[(**h).clone(), (**t).clone()])
                .into_iter()
                .map(|(mut qs, a)| {
                    let t = qs.pop().unwrap();
                    let h = qs.pop().unwrap();
                    (with(PatKind::Cons(Box::new(h), Box::new(t))), a)
                })
                .collect(),
            PatKind::Record(n, fs) => {
                let ps: Vec<Pattern> = fs.iter().map(|(_, p)| p.clone()).collect();
                Self::expand_seq(&ps)
                    .into_iter()
                    .map(|(qs, a)| {
                        let fs = fs.iter().map(|(f, _)| f.clone()).zip(qs).collect();
                        (with(PatKind::Record(n.clone(), fs)), a)
                    })
                    .collect()
            }
            _ => vec![(p.clone(), vec![])],
        }
    }

    fn expand_or<'a>(row: Row<'a>) -> Vec<Row<'a>> {
        for (i, (occ, p)) in row.pats.iter().enumerate() {
            if let PatKind::Or(alts) = &p.kind {
                let mut out = Vec::new();
                for a in alts {
                    let mut r = row.clone();
                    r.pats[i] = (*occ, a.clone());
                    r.alts.push(a.span);
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
                PatKind::Wild => {}
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
            PatKind::Unit => Column::Unit,
            PatKind::Lit(_) | PatKind::Neg(_) => Column::Lit,
            _ => match self.seq_column(cx, &rows, occ) {
                Some(m) => Column::Seq(m),
                None => Column::Con,
            },
        };
        match col {
            Column::Tuple => self.compile_tuple(cx, rows, occ, &pat, expected, tail),
            Column::Unit => self.compile_unit(cx, rows, occ, &pat, expected, tail),
            Column::Lit => self.compile_lit(cx, rows, occ, expected, tail),
            Column::Con => self.compile_con(cx, rows, occ, &pat, expected, tail),
            Column::Seq(m) => {
                if self.mixed_seq(cx, &rows, occ) {
                    return Tm::Error;
                }
                self.compile_seq(cx, rows, occ, m, expected, tail)
            }
        }
    }

    fn leaf(&mut self, cx: &mut Cx, rows: Vec<Row>, expected: &Val, tail: bool) -> Tm {
        let row = rows[0].clone();
        if self.pm.unreached {
            // A row no value reaches: its pattern is checked; its guard and
            // body once for the arm.
            if self.pm.bodies.contains(&row.span) {
                return Tm::Error;
            }
        } else {
            if !self.pm.reached.contains(&row.span) {
                self.pm.reached.push(row.span);
            }
            let mut alts = row.alts.clone();
            alts.sort_by_key(|a| a.start);
            self.pm.reached_rows.push((row.span, alts));
            let region = match row.body {
                ArmBody::Expr(e) => e.span,
                ArmBody::Rest(_, r) => r.span,
            };
            let before = self.pm.facts_before;
            self.probe(cx, row.span, ProbeKind::Arm, row.span.to(region), before);
            self.check_dropped(cx, &row);
        }
        if !self.pm.bodies.contains(&row.span) {
            self.pm.bodies.push(row.span);
        }
        let start = cx.lvl();
        let mut lets = Vec::new();
        for (name, occ, at) in &row.binds {
            let ty = cx.ty_of(*occ);
            let v = cx.env[*occ].clone();
            let tyt = quote(&self.g, cx.lvl(), &ty);
            let t = cx.var(*occ);
            let mult = self.named_mult(cx, name, &ty, *at, Mult::Many);
            let l = cx.define(name, ty, v, mult);
            cx.locals[l].sub = cx.locals[*occ].sub;
            cx.locals[l].sub_cond = cx.locals[*occ].sub_cond;
            cx.locals[l].param = cx.locals[*occ].param;
            self.bound_at(cx, l, *at);
            lets.push((self.binder_name(name, *at), mult, tyt, t));
        }
        let wrap = |lets: &[(crate::core::Name, Mult, Tm, Tm)], body: Tm| {
            let mut t = body;
            for (n, mult, tyt, v) in lets.iter().rev() {
                t = Tm::Let(n.clone(), *mult, Rc::new(tyt.clone()), Rc::new(v.clone()), Rc::new(t));
            }
            t
        };
        match row.guard {
            None => {
                let body = self.arm_body(cx, row.body, expected, tail);
                cx.truncate(start);
                wrap(&lets, body)
            }
            Some(g) => {
                let b = self.bool_ty();
                let gt = self.check(cx, g, &b, false);
                let gv = self.eval(cx, &gt);
                let saved = cx.facts.len();
                cx.assume(self.is_bool(gv.clone(), true));
                let bt = self.arm_body(cx, row.body, expected, tail);
                cx.facts.truncate(saved);
                // The arm's names are bound twice: for the guard and for the
                // body, so that when the guard is false the next arms see the
                // value unused. A resource bound for the guard is ghost there:
                // the guard can't use it up before the body runs.
                cx.truncate(start);
                cx.assume(self.is_bool(gv, false));
                let rest: Vec<Row> = rows[1..].to_vec();
                let et = if rest.is_empty() {
                    let w = self.render_path();
                    self.uncovered(cx, if w == "_" {
                        "the case where the guard is false".to_string()
                    } else {
                        format!("`{w}` when the guard is false")
                    });
                    Tm::Error
                } else {
                    self.compile(cx, rest, expected, tail)
                };
                cx.facts.truncate(saved);
                if let Some(f) = self.cur_fn {
                    for (n, m, _, _) in &lets {
                        if *m == Mult::One {
                            self.guard_vars.insert((f, n.to_string()), g.span);
                        }
                    }
                }
                let guard_lets: Vec<(crate::core::Name, Mult, Tm, Tm)> = lets
                    .iter()
                    .map(|(n, m, tyt, v)| (n.clone(), if *m == Mult::One { Mult::Zero } else { *m }, tyt.clone(), v.clone()))
                    .collect();
                self.if_tm(wrap(&guard_lets, gt), wrap(&lets, bt), et)
            }
        }
    }

    /// E0404: at a leaf, every resource reached by the match must be taken
    /// apart further or bound to a name.
    fn check_dropped(&mut self, cx: &Cx, row: &Row) {
        let mut occs: Vec<usize> = self.pm.roots.iter().copied().filter(|r| cx.locals[*r].name.starts_with('$')).collect();
        for (_, f) in &self.pm.frames {
            match f {
                Frame::Ctor(_, fs) | Frame::Tuple(fs) => occs.extend(fs.iter().copied()),
                Frame::Seq(u) => occs.push(*u),
            }
        }
        // A part of a value bound whole (`other` in a later arm) isn't dropped.
        let parent = |o: usize| {
            self.pm.frames.iter().find_map(|(p, f)| match f {
                Frame::Ctor(_, fs) | Frame::Tuple(fs) => fs.contains(&o).then_some(*p),
                Frame::Seq(u) => (*u == o).then_some(*p),
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
                let ty = cx.ty_of(o);
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

    /// `let (x, fs) = op fs` where `fs` holds no resource: an operation on
    /// an authority (`Fs`, `Term`, …) returns only its result (D171).
    fn authority_hint(&mut self, cx: &Cx, pat: &Pattern, ps: &[Pattern], occ: usize) {
        let Some(PatKind::Var(name)) = ps.last().map(|p| &p.kind) else { return };
        let Some(l) = cx.lookup(name) else { return };
        if l >= occ || self.val_linear(&cx.locals[l].ty.clone()) {
            return;
        }
        let first = match ps.first().map(|p| &p.kind) {
            Some(PatKind::Var(x)) if ps.len() == 2 => x.clone(),
            _ => "x".into(),
        };
        if let Some((_, d)) = self.diags.last_mut() {
            if d.code == "E0201" && d.span == pat.span && d.help.is_none() {
                d.help = Some(format!(
                    "`{name}` is not a resource, so an operation on it returns only its result: `let {first} = …`"
                ));
            }
        }
    }

    /// `()` takes nothing apart: the value has type `()`, and every row with
    /// `()` here matches it.
    fn compile_unit(&mut self, cx: &mut Cx, rows: Vec<Row>, occ: usize, pat: &Pattern, expected: &Val, tail: bool) -> Tm {
        let ty = cx.ty_of(occ);
        let unit = self.unit();
        if !self.unify_at(cx, &ty, &unit, pat.span, "this pattern") {
            self.pm.bad = true;
            return Tm::Error;
        }
        let rows = rows
            .into_iter()
            .map(|mut r| {
                r.pats.retain(|(o, p)| !(*o == occ && matches!(p.kind, PatKind::Unit)));
                r
            })
            .collect();
        self.compile(cx, rows, expected, tail)
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
        // Rows may take the tuple apart into different numbers of parts:
        // split at the fewest, the longer patterns' tails as one (`(x, y, z)`
        // is `(x, (y, z))`, D174).
        let n = rows
            .iter()
            .flat_map(|r| r.pats.iter())
            .filter_map(|(o, p)| match &p.kind {
                PatKind::Tuple(qs) if *o == occ && qs.len() >= 2 => Some(qs.len()),
                _ => None,
            })
            .min()
            .unwrap_or(ps.len());
        let ty = match self.force(&cx.ty_of(occ)) {
            Val::TupleTy(ts) => Val::TupleTy(crate::core::flat_parts(&self.g, &ts, true).into()),
            t => t,
        };
        let comps_ty = match ty {
            Val::TupleTy(ts) if ts.len() == n => ts,
            // `()` has no parts at all.
            Val::TupleTy(ts) if ts.is_empty() => {
                self.pat_err(
                    Diagnostic::error("E0246", format!("this pattern has {n} parts, but `()` has none"), pat.span)
                        .with_help("match `()` with the pattern `()`, or `_`"),
                );
                return Tm::Error;
            }
            // A tuple type with fewer parts than the pattern, ending in a
            // type that isn't a tuple: the pattern has too many parts.
            Val::TupleTy(ts) if ts.len() < n && !matches!(self.force(&ts[ts.len() - 1]), Val::Neutral(..)) => {
                let shown = self.show_val(cx, &Val::TupleTy(ts.clone()));
                self.pat_err(
                    Diagnostic::error("E0246", format!("this pattern has {n} parts, but `{shown}` has {}", ts.len()), pat.span)
                        .with_help(format!("take it apart into {} parts, or fewer: the last part is then the rest", ts.len())),
                );
                self.pm.bad = true;
                return Tm::Error;
            }
            other => {
                // The occurrence's type can't depend on the occurrence itself.
                let mut outer = cx.clone();
                outer.truncate(occ);
                let metas: Rc<[Val]> = (0..n).map(|_| self.fresh_meta_val(&outer)).collect();
                let want = Val::TupleTy(metas.clone());
                if !self.unify_at(cx, &other, &want, pat.span, "this pattern") {
                    self.authority_hint(cx, pat, ps, occ);
                    self.pm.bad = true;
                    return Tm::Error;
                }
                metas
            }
        };
        let start = cx.lvl();
        let mut lets = Vec::new();
        let mut comps = Vec::new();
        let comps_ty: Vec<Val> = comps_ty.iter().map(|t| self.reduce_type(t)).collect();
        for (i, cty) in comps_ty.into_iter().enumerate() {
            let tm = Tm::Proj(Rc::new(cx.var(occ)), i, i + 1 == n);
            let v = self.eval(cx, &tm);
            let tyt = quote(&self.g, cx.lvl(), &cty);
            let l = cx.define(&format!("$c{i}"), cty, v, Mult::Many);
            cx.locals[l].sub = cx.locals[occ].sub;
            cx.locals[l].sub_cond = cx.locals[occ].sub_cond;
            comps.push(l);
            lets.push((format!("$c{i}"), tyt, tm));
        }
        let mut new_rows = Vec::new();
        for mut r in rows {
            if let Some(i) = r.pats.iter().position(|(o, _)| *o == occ) {
                let (_, p) = r.pats.remove(i);
                let p = match p.kind {
                    PatKind::Tuple(mut qs) if qs.len() > n => {
                        let tail: Vec<Pattern> = qs.split_off(n - 1);
                        let span = tail[0].span.to(tail[tail.len() - 1].span);
                        qs.push(Pattern { kind: PatKind::Tuple(tail), span });
                        Pattern { kind: PatKind::Tuple(qs), span: p.span }
                    }
                    _ => p,
                };
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
                let n = self.number(s);
                (Lit::int(n), Val::Error)
            }
            PatKind::Neg(s) => {
                let n = self.number(s);
                (Lit::int(-n), self.int())
            }
            PatKind::Lit(ast::Lit::Byte(b)) => (Lit::Num(*b as i128), self.nat()),
            PatKind::Lit(ast::Lit::Char(c)) => (Lit::Num(*c as i128), self.nat()),
            PatKind::Lit(ast::Lit::Str(s)) => (Lit::Str(Rc::from(s.as_str())), self.string()),
            PatKind::Lit(ast::Lit::Bytes(b)) => (Lit::Bytes(Rc::from(b.as_slice())), self.bytes()),
            _ => return None,
        })
    }

    fn compile_lit(&mut self, cx: &mut Cx, rows: Vec<Row>, occ: usize, expected: &Val, tail: bool) -> Tm {
        let occ_ty = cx.ty_of(occ);
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
            self.uncovered(cx, if w == "_" {
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

    /// The constructor a pattern's name means: one of the type of the value
    /// matched (`hint`), whether or not it is imported; else one in scope.
    /// An abstract type of another module shows no constructors (D155).
    fn pattern_con(&self, name: &str, hint: Option<TyId>) -> Option<ConId> {
        if let Some(t) = hint.filter(|t| self.sealed_from(*t).is_none()) {
            let ti = &self.g.tys[t.0 as usize];
            if let Some(c) = ti.ctors.iter().find(|c| *self.g.cons[c.0 as usize].name == *name) {
                return Some(*c);
            }
        }
        match self.resolve(name, false) {
            Some(Sym::Con(c)) => Some(c),
            _ => None,
        }
    }

    /// The constructor a pattern names, and its sub-patterns (None for record patterns).
    fn pat_ctor(&mut self, p: &Pattern, hint: Option<TyId>) -> Option<(ConId, Option<Vec<Pattern>>)> {
        let wk = self.g.well_known.clone();
        let unknown = |this: &mut Self, name: &ast::Ident| {
            // A constructor of an abstract type of another module (D155).
            if let Some(t) = hint.filter(|t| this.sealed_from(*t).is_some()) {
                let ti = &this.g.tys[t.0 as usize];
                let d = if ti.ctors.iter().any(|c| *this.g.cons[c.0 as usize].name == *name.name) {
                    this.sealed_error(t, "constructors", name.span)
                } else {
                    Diagnostic::error("E0244", format!("unknown constructor `{}`", name.name), name.span)
                };
                this.pat_err(d);
                return;
            }
            let mut d = Diagnostic::error("E0244", format!("unknown constructor `{}`", name.name), name.span);
            if let Some(t) = hint {
                let ti = &this.g.tys[t.0 as usize];
                let names: Vec<String> = ti.ctors.iter().map(|c| format!("`{}`", this.g.cons[c.0 as usize].name)).collect();
                d = d.with_help(format!("the constructors of `{}` are {}", ti.name, names.join(", ")));
            }
            this.pat_err(d);
        };
        match &p.kind {
            PatKind::Con(name, args) if name.name == SEQ_NONE => Some((wk.none?, Some(args.clone()))),
            PatKind::Con(name, args) if name.name == SEQ_SOME => Some((wk.some?, Some(args.clone()))),
            PatKind::Con(name, args) => match self.pattern_con(&name.name, hint) {
                Some(c) => {
                    self.index_pattern(name.span, index::Target::Con(c));
                    Some((c, Some(args.clone())))
                }
                _ => {
                    unknown(self, name);
                    None
                }
            },
            PatKind::Record(name, _) => match self.pattern_con(&name.name, hint) {
                Some(c) => {
                    self.index_pattern(name.span, index::Target::Con(c));
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
        let occ_ty = self.force(&cx.ty_of(occ));
        let hint = match &occ_ty {
            Val::TyCon(t, _) => Some(*t),
            _ => None,
        };
        let Some((c0, _)) = self.pat_ctor(pat, hint) else { return Tm::Error };
        let tid = self.g.cons[c0.0 as usize].ty;
        let params = match occ_ty {
            Val::TyCon(t, ps) if t == tid => ps,
            Val::Error => {
                self.pm.bad = true;
                return Tm::Error;
            }
            other => {
                let n = self.g.arity_ty(tid);
                let mut outer = cx.clone();
                outer.truncate(occ);
                let metas: Rc<[Val]> = (0..n).map(|_| self.fresh_meta_val(&outer)).collect();
                let want = Val::TyCon(tid, metas.clone());
                if unify(&self.g, cx.lvl(), &other, &want).is_err() {
                    let shown = self.show_val(cx, &other);
                    let cname = self.g.cons[c0.0 as usize].name.clone();
                    let tname = self.g.tys[tid.0 as usize].name.clone();
                    let mut d = Diagnostic::error(
                        "E0241",
                        format!("`{cname}` is a constructor of `{tname}`, but the value being matched has type `{shown}`"),
                        pat.span,
                    )
                    .with_label(format!("expected a `{shown}` pattern"));
                    if matches!(pat.kind, PatKind::List(_) | PatKind::Cons(..)) {
                        d = d.with_help(format!(
                            "`[]` and `x :: rest` take apart a list, or a value of a type with a `Seq` instance; `{shown}` has none"
                        ));
                    }
                    self.pat_err(d);
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
            let mut env: Vec<Val> = params.to_vec();
            let mut lvls = Vec::new();
            let sub = cx.locals[occ].sub.or(cx.locals[occ].param);
            let sub_cond = if cx.locals[occ].sub.is_some() { cx.locals[occ].sub_cond } else { None };
            for (n, m, _, fty) in &fields {
                let ty = eval(&self.g, &Rc::new(env.clone()), fty);
                let mult = if *m == Mult::Zero { Mult::Zero } else { Mult::Many };
                let l = cx.bind(&format!("${n}"), ty, mult);
                cx.locals[l].sub = sub;
                cx.locals[l].sub_cond = sub_cond;
                cx.locals[l].comptime = occ_static;
                env.push(Val::var(l));
                lvls.push(l);
            }
            let explicit: Vec<usize> =
                fields.iter().zip(&lvls).filter(|(f, _)| f.2 == Icit::Expl).map(|(_, l)| *l).collect();
            let mut rs = Vec::new();
            // Where a row names this constructor.
            let mut named: Vec<Span> = Vec::new();
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
                named.push(p.span);
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
                        let expl_k = fields.iter().enumerate().filter(|(_, f)| f.2 == Icit::Expl).map(|(k, _)| k);
                        for (k, a) in expl_k.zip(&args) {
                            if !matches!(a.kind, PatKind::Wild) {
                                self.reference(a.span, index::Target::Field(c, k), super::unused::RefKind::Read);
                            }
                        }
                        explicit.iter().copied().zip(args).collect()
                    }
                    (None, PatKind::Record(_, fps)) => {
                        let mut v = Vec::new();
                        for (fname, fp) in fps {
                            match fields.iter().position(|f| f.0.as_ref() == fname.name) {
                                Some(k) => {
                                    if !matches!(fp.kind, PatKind::Wild) {
                                        self.reference(fname.span, index::Target::Field(c, k), super::unused::RefKind::Read);
                                    }
                                    v.push((lvls[k], fp.clone()))
                                }
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
            let all: Rc<[Val]> = params.iter().cloned().chain(fvals).collect();
            let occ_val = cx.env[occ].clone();
            cx.assume(Self::prim_val(Prim::Eq, vec![occ_val, Val::Con(c, all.clone())]));
            for inv in self.con_invs.get(&c).cloned().unwrap_or_default() {
                let f = self.inst_pred(&inv, all.to_vec());
                cx.assume(f);
            }
            // Its type equations (#209), at this value's type: they hold in
            // the arm, unless the type contradicts them, and then the case
            // can't occur.
            let givens_before = self.givens.len();
            let mut never = false;
            if let Some(teqs) = self.con_teqs.get(&c).cloned() {
                let env = Rc::new(all.to_vec());
                let eqs = teqs.iter().map(|q| (eval(&self.g, &env, &q.lhs), eval(&self.g, &env, &q.rhs), q.text.clone())).collect();
                self.assume_teqs(eqs);
                if self.contradiction().is_some() {
                    self.givens.truncate(givens_before);
                    never = true;
                    for at in &named {
                        let built = self.built_type(cx, c, &teqs, &all);
                        let here = self.show_val(cx, &Val::TyCon(tid, params.clone()));
                        let cname = self.g.cons[c.0 as usize].name.to_string();
                        self.err(
                            Diagnostic::warning(
                                "W022",
                                format!(
                                    "this arm never runs: `{cname}` builds {} `{built}`, and this is {} `{here}`",
                                    super::tyeq::article(&built),
                                    super::tyeq::article(&here)
                                ),
                                *at,
                            )
                            .with_label("this case can't occur"),
                        );
                    }
                }
            }
            // Dependent matching: where the matched value is a variable, the
            // expected type sees it as this constructor (`f~format_type ps`
            // becomes `f~format_type []` in the `[]` arm).
            // Only a type that mentions the variable, and has no unknowns
            // left (an unknown abstracts over the variable itself).
            let refined = if cx.locals[occ].bound {
                let tm = quote(&self.g, cx.lvl(), expected);
                if !super::has_meta(&tm) && mentions_var(&tm, cx.lvl() - 1 - occ) {
                    let mut env = cx.env.to_vec();
                    env[occ] = Val::Con(c, all.clone());
                    eval(&self.g, &Rc::new(env), &tm)
                } else {
                    expected.clone()
                }
            } else {
                expected.clone()
            };
            // So do the types of the variables in scope (D173): `x~futures s a`
            // is a `Future a` in the `One` arm of `match s`, as in Agda and
            // Idris. Only the type changes; the variable is the same.
            // A type that still mentions the fields (`p~(x~a -> Bool,
            // list.contains xs x)` in the `x :: rest` arm) mentions locals
            // bound after the variable: it is the type its uses have
            // (`refined`), and `ty` stays over the locals before it.
            let mut retyped: Vec<(usize, Val, Option<Val>)> = Vec::new();
            if cx.locals[occ].bound {
                let i = cx.lvl() - 1 - occ;
                for l in 0..start {
                    if l == occ {
                        continue;
                    }
                    let tm = quote(&self.g, cx.lvl(), &cx.ty_of(l));
                    if !super::has_meta(&tm) && mentions_var(&tm, i) {
                        let mut env = cx.env.to_vec();
                        env[occ] = Val::Con(c, all.clone());
                        let ty = eval(&self.g, &Rc::new(env), &tm);
                        let new = quote(&self.g, cx.lvl(), &ty);
                        if let Some(f) = self.cur_fn {
                            if self.type_linear(&tm) && self.never_linear(&new) {
                                self.moot_in_arm.insert((f, occ, c, l));
                            }
                        }
                        let saved = (cx.locals[l].ty.clone(), cx.locals[l].refined.clone());
                        if mentions_level_from(&new, cx.lvl(), l) {
                            cx.locals[l].refined = Some(ty);
                        } else {
                            cx.locals[l].ty = ty;
                            cx.locals[l].refined = None;
                        }
                        retyped.push((l, saved.0, saved.1));
                    }
                }
            }
            let body = if rs.is_empty() {
                // A case its type equations rule out needn't be covered (#209).
                if !never {
                    let w = self.render_path();
                    self.uncovered(cx, format!("`{w}`"));
                }
                Tm::Error
            } else {
                self.compile(cx, rs, &refined, tail)
            };
            self.givens.truncate(givens_before);
            for (l, ty, refined) in retyped {
                cx.locals[l].ty = ty;
                cx.locals[l].refined = refined;
            }
            cx.facts.truncate(saved);
            self.pm.frames.pop();
            cx.truncate(start);
            branches.push((c, fields.len(), body));
        }
        Tm::Case(Rc::new(scrut), Rc::new(CaseTm { branches, lits: vec![], default: None }))
    }
}

impl Elab {
    /// `Seq.uncons`, if the rows take occurrence `occ` apart with `[]` or
    /// `x :: rest` and its type isn't a list but has a `Seq` instance or a
    /// clause in scope (§9.8). A list, or a type not known yet, is matched
    /// as a list, built in.
    fn seq_column(&mut self, cx: &Cx, rows: &[Row], occ: usize) -> Option<DefId> {
        let any_seq = rows
            .iter()
            .flat_map(|r| r.pats.iter())
            .any(|(o, p)| *o == occ && matches!(p.kind, PatKind::List(_) | PatKind::Cons(..)));
        if !any_seq {
            return None;
        }
        let ty = self.force(&cx.ty_of(occ));
        if matches!(&ty, Val::TyCon(t, _) if Some(*t) == self.g.well_known.list) {
            return None;
        }
        self.operator_method(cx, "Seq", "uncons", &ty)
    }

    /// E0248 if the rows mix sequence patterns with the type's own
    /// constructors at `occ`.
    fn mixed_seq(&mut self, cx: &Cx, rows: &[Row], occ: usize) -> bool {
        let Some(con) = rows
            .iter()
            .flat_map(|r| r.pats.iter())
            .find(|(o, p)| *o == occ && matches!(p.kind, PatKind::Con(..) | PatKind::Record(..)))
            .map(|(_, p)| p.span)
        else {
            return false;
        };
        let shown = self.show_val(cx, &cx.ty_of(occ));
        self.pat_err(
            Diagnostic::error("E0248", format!("this `match` takes a `{shown}` apart both with `[]` or `::` and with its constructors"), con)
                .with_label(format!("a constructor of `{shown}`"))
                .with_note(format!("`[]` and `x :: rest` take a `{shown}` apart with `Seq.uncons`, not with its constructors"))
                .with_help("use one kind of pattern in each `match`"),
        );
        true
    }

    /// `Seq.size` of occurrence `occ`, a measure to guess for the
    /// function (§5.3): `call`, `uncons` applied to it, with `size` for
    /// `uncons` (the two take the same implicit arguments).
    fn note_seq_size(&mut self, cx: &Cx, call: &Tm, occ: usize) {
        let Some(f) = self.cur_fn else { return };
        let Some(prelude) = self.modules.get("std.prelude") else { return };
        let Some(Sym::Def(size)) = prelude.values.get("size").copied() else { return };
        fn head_to(t: &Tm, to: DefId) -> Option<Tm> {
            match t {
                Tm::App(a, b, i, m) => Some(Tm::App(Rc::new(head_to(a, to)?), b.clone(), *i, *m)),
                Tm::Def(_) => Some(Tm::Def(to)),
                _ => None,
            }
        }
        let Some(t) = head_to(call, size) else { return };
        let text = format!("Seq.size {}", cx.locals[occ].name);
        let v = self.seq_sizes.entry(f).or_default();
        if !v.iter().any(|(_, _, x)| *x == text) {
            v.push((t, cx.lvl(), text));
        }
    }

    /// Take occurrence `occ` apart with `uncons` (`m`): bind its result
    /// once, and match `None` for `[]` and `Some (p, q)` for `p :: q`
    /// (§9.8). Rest patterns are taken apart again in the same way.
    fn compile_seq(&mut self, cx: &mut Cx, rows: Vec<Row>, occ: usize, m: DefId, expected: &Val, tail: bool) -> Tm {
        let span = self.match_span;
        let occ_ty = cx.ty_of(occ);
        let (f, fty) = self.sym_term(cx, Sym::Def(m), span);
        self.name_span = span;
        let (f, fty) = self.insert(cx, f, fty);
        let (call, rty) = self.apply_tm(cx, f, fty, cx.var(occ), &occ_ty, span);
        // At a known instance its dictionary, found now, gives the element
        // type (`Char` for a string), which the patterns' variables have.
        self.solve_instances(false);
        let rty = self.reduce_type(&rty);
        self.note_seq_size(cx, &call, occ);
        let start = cx.lvl();
        let v = self.eval(cx, &call);
        let tyt = quote(&self.g, cx.lvl(), &rty);
        let u = cx.define("$uncons", rty, v, Mult::Many);
        let mut new_rows = Vec::new();
        for mut r in rows {
            if let Some(i) = r.pats.iter().position(|(o, _)| *o == occ) {
                let (_, p) = r.pats.remove(i);
                let con = |name: &str, args: Vec<Pattern>| Pattern {
                    kind: PatKind::Con(ast::Ident { name: name.to_string(), span: p.span }, args),
                    span: p.span,
                };
                let pair = |h: Pattern, t: Pattern| {
                    let span = h.span.to(t.span);
                    con(SEQ_SOME, vec![Pattern { kind: PatKind::Tuple(vec![h, t]), span }])
                };
                let q = match p.kind {
                    PatKind::List(ref items) if items.is_empty() => con(SEQ_NONE, vec![]),
                    PatKind::List(ref items) => {
                        let rest = Pattern { kind: PatKind::List(items[1..].to_vec()), span: p.span };
                        pair(items[0].clone(), rest)
                    }
                    PatKind::Cons(ref h, ref t) => pair((**h).clone(), (**t).clone()),
                    _ => unreachable!("mixed_seq ruled out other patterns"),
                };
                r.pats.insert(i, (u, q));
            }
            new_rows.push(r);
        }
        self.pm.frames.push((occ, Frame::Seq(u)));
        let body = self.compile(cx, new_rows, expected, tail);
        self.pm.frames.pop();
        cx.truncate(start);
        Tm::Let(Rc::from("$uncons"), Mult::Many, Rc::new(tyt), Rc::new(call), Rc::new(body))
    }
}

/// Does `t`, a term over `total` locals, mention a local at level `from`
/// or above?
fn mentions_level_from(t: &Tm, total: usize, from: usize) -> bool {
    let mut free = std::collections::BTreeSet::new();
    crate::core::free_vars(t, 0, &mut free);
    free.iter().any(|i| *i < total && total - 1 - i >= from)
}

/// Does `t` mention variable `i` (de Bruijn, at its top)?
fn mentions_var(t: &Tm, i: usize) -> bool {
    match t {
        Tm::Var(j) => *j == i,
        _ => t.any_sub(|x, n| mentions_var(x, i + n)),
    }
}
