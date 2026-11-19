//! Termination (§5.3): structural recursion, `decreasing` measures, `partial`,
//! and measures guessed for recursion that is none of these (D150).

use super::*;

/// A call between two functions of the module, neither with a measure: what
/// a guessed measure must make smaller (D150).
#[derive(Clone)]
pub struct RecCall {
    pub caller: DefId,
    pub callee: DefId,
    /// The callee's binders' values (implicit ones first).
    pub args: Vec<Val>,
    /// Where it is, with the facts there; its goal is filled in per measure.
    pub ob: Obligation,
}

/// A measure: its components over a function's binders, and its text.
pub type Measure = (Vec<Tm>, String);

/// A recursive group whose measure is guessed in the proofs phase (D150).
#[derive(Clone)]
pub struct GuessGroup {
    pub module: String,
    pub members: Vec<DefId>,
    /// Each member's candidates, in the order they are tried.
    pub candidates: Vec<Vec<Measure>>,
    pub calls: Vec<RecCall>,
}

impl Elab {
    /// A call that may be recursion with no measure written (D150).
    pub fn note_rec_call(&mut self, cx: &Cx, callee: DefId, args: &[Rc<Tm>], span: Span) {
        let Some(caller) = self.cur_fn else { return };
        if self.in_spec > 0 {
            return;
        }
        let total = |m: Option<&FnMeta>| m.is_some_and(|m| !m.partial && !m.decreasing);
        if !total(self.fn_meta.get(&caller)) || !total(self.fn_meta.get(&callee)) || *self.g.defs[callee.0 as usize].module != *self.cur {
            return;
        }
        let args: Vec<Val> = args.iter().map(|a| self.eval(cx, a)).collect();
        let name = self.g.defs[caller.0 as usize].name.to_string();
        let ob = self.obligation(cx, span, ObKind::Measure { func: name, measure: String::new() }, String::new(), Val::Error, None);
        self.rec_calls.push(RecCall { caller, callee, args, ob });
    }

    pub fn check_termination(&mut self) {
        let fns: Vec<DefId> = std::mem::take(&mut self.module_fns);
        let calls: Vec<CallRec> = std::mem::take(&mut self.calls);
        let rec_calls: Vec<RecCall> = std::mem::take(&mut self.rec_calls);
        let idx: HashMap<DefId, usize> = fns.iter().enumerate().map(|(i, d)| (*d, i)).collect();
        let n = fns.len();
        let mut edges: Vec<Vec<usize>> = vec![Vec::new(); n];
        for c in &calls {
            if let (Some(&a), Some(&b)) = (idx.get(&c.caller), idx.get(&c.callee)) {
                edges[a].push(b);
            }
        }

        // A total function may not call a partial one.
        for c in &calls {
            let caller = self.fn_meta.get(&c.caller).cloned().unwrap_or_default();
            let callee = self.fn_meta.get(&c.callee).cloned().unwrap_or_default();
            if !caller.partial && callee.partial {
                self.err(
                    Diagnostic::error(
                        "E0302",
                        format!("`{}` is `partial` (it may not terminate), so `{}` cannot call it", callee.name, caller.name),
                        c.span,
                    )
                    .with_help(format!("mark `{}` as `partial fn` too", caller.name)),
                );
            }
        }

        for scc in super::order::sccs(&edges) {
            let recursive = scc.len() > 1 || edges[scc[0]].contains(&scc[0]);
            if !recursive {
                continue;
            }
            let members: Vec<DefId> = scc.iter().map(|&i| fns[i]).collect();
            let metas: Vec<FnMeta> = members.iter().map(|d| self.fn_meta.get(d).cloned().unwrap_or_default()).collect();
            if metas.iter().all(|m| m.partial || m.decreasing) {
                // `decreasing` measures are proof obligations at each call in the group (§5.3).
                let total: Vec<DefId> = members.iter().zip(&metas).filter(|(_, m)| !m.partial).map(|(d, _)| *d).collect();
                for (caller, callee, ob) in std::mem::take(&mut self.measure_obs) {
                    if total.contains(&caller) && total.contains(&callee) {
                        self.obligations.push(ob);
                    } else {
                        self.measure_obs.push((caller, callee, ob));
                    }
                }
                // A recursive use that isn't a full call can't have its measure checked.
                for c in calls.iter().filter(|c| total.contains(&c.caller) && members.contains(&c.callee)) {
                    if !self.saturated_heads.contains(&c.span) {
                        let name = self.fn_meta.get(&c.callee).map(|m| m.name.clone()).unwrap_or_default();
                        self.err(
                            Diagnostic::error(
                                "E0303",
                                format!("`{name}` is used here as a value, so its `decreasing` measure can't be checked"),
                                c.span,
                            )
                            .with_label("recursive use without all its arguments")
                            .with_help("call it with all its arguments here, e.g. inside a lambda, or make the recursion structural"),
                        );
                    }
                }
                continue;
            }
            let inner: Vec<&CallRec> = calls
                .iter()
                .filter(|c| members.contains(&c.caller) && members.contains(&c.callee))
                .collect();
            if structural(&members, &metas, &inner) {
                continue;
            }
            // Recursion through an instance's dictionary (D136): a use of
            // the class's function at the instance's own type.
            if let Some(c) = inner.iter().find(|c| self.dict_defs.contains(&c.callee) && !self.dict_defs.contains(&c.caller)) {
                let inst = self.g.defs[c.callee.0 as usize].name.to_string();
                let caller = self.fn_meta.get(&c.caller).map(|m| m.name.clone()).unwrap_or_default();
                let own = caller.rsplit('.').next().unwrap_or("").to_string();
                self.err(
                    Diagnostic::error("E0301", format!("`{caller}` uses `instance {inst}` itself, so it can't be shown to terminate"), c.span)
                        .with_label("the class's function at this instance's own type")
                        .with_help(format!("inside the instance, call its own `{own}` (on a smaller part of a parameter), which is checked like any recursion")),
                );
                continue;
            }
            // No measure written: one is guessed, and proved, later (D150).
            if self.guess_measure(&members, &metas, &inner, &rec_calls) {
                continue;
            }
            // Report at the first recursive call made by a function without `decreasing`.
            let bad = inner
                .iter()
                .find(|c| {
                    let k = members.iter().position(|d| *d == c.caller).unwrap();
                    !metas[k].partial && !metas[k].decreasing
                })
                .copied();
            if let Some(c) = bad {
                let k = members.iter().position(|d| *d == c.caller).unwrap();
                let name = metas[k].name.clone();
                let msg = if members.len() == 1 {
                    format!("cannot show that `{name}` terminates: no argument gets structurally smaller in this recursive call")
                } else {
                    let names: Vec<String> = metas.iter().map(|m| format!("`{}`", m.name)).collect();
                    format!(
                        "cannot show that {} terminate: they call each other, and no argument gets structurally smaller",
                        names.join(", ")
                    )
                };
                let is_lemma = !metas[k].is_fn;
                let (msg, label, help) = if is_lemma {
                    (
                        format!("`{name}` uses itself, but not on a smaller argument, so this is not an induction"),
                        "the induction hypothesis".to_string(),
                        format!(
                            "use `{name}` only on a part of a parameter you matched on, such as `rest` in `x :: rest`, or add `decreasing <measure>` as the first line of its proof"
                        ),
                    )
                } else {
                    (
                        msg,
                        "recursive call".to_string(),
                        format!(
                            "recurse on a part of a parameter you matched on, or add `decreasing <measure>` as the first line of `{name}`, or mark it `partial`"
                        ),
                    )
                };
                self.err(Diagnostic::error("E0301", msg, c.span).with_label(label).with_help(help));
            }
        }
    }
}

impl Elab {
    /// Set up guessing a measure for a recursive group with none written
    /// (D150): every member a total function, every recursive call a full
    /// call, and candidates for each. False if it can't be.
    fn guess_measure(&mut self, members: &[DefId], metas: &[FnMeta], inner: &[&CallRec], rec_calls: &[RecCall]) -> bool {
        if metas.iter().any(|m| m.partial || m.decreasing) {
            return false;
        }
        let calls: Vec<RecCall> =
            rec_calls.iter().filter(|c| members.contains(&c.caller) && members.contains(&c.callee)).cloned().collect();
        // Each recursive call must be one we can compare measures at.
        if inner.iter().any(|c| !calls.iter().any(|r| r.ob.span == c.span || r.ob.span.start <= c.span.start && c.span.end <= r.ob.span.end)) {
            return false;
        }
        let mut candidates = Vec::new();
        for d in members {
            let own: Vec<&RecCall> = calls.iter().filter(|c| c.caller == *d).collect();
            let cs = self.measure_candidates(*d, &own);
            if cs.is_empty() {
                return false;
            }
            candidates.push(cs);
        }
        self.guessed.extend(members.iter().copied());
        self.guess_groups.push(GuessGroup { module: self.cur.clone(), members: members.to_vec(), candidates, calls });
        true
    }

    /// The measures to try for `d` (D150 a): its parameters' sizes, the
    /// distances the comparisons guarding its recursive calls bound, and
    /// sums of two sizes; each over `d`'s binders.
    fn measure_candidates(&self, d: DefId, calls: &[&RecCall]) -> Vec<Measure> {
        let Some(spec) = self.specs.get(&d) else { return Vec::new() };
        let n = spec.n_binders;
        let wk = &self.g.well_known;
        // The binders' names, for the measures' text.
        let mut names: Vec<Name> = Vec::new();
        let mut sizes: Vec<Measure> = Vec::new();
        let mut ty = self.g.defs[d.0 as usize].ty.clone();
        let mut k = 0;
        while let Tm::Pi(x, _, icit, dom, body) = ty.clone() {
            if k >= n {
                break;
            }
            let env: Env = Rc::new((0..k).map(Val::var).collect());
            let dv = self.force(&crate::core::eval(&self.g, &env, &dom));
            let var = Tm::Var(n - 1 - k);
            if icit == Icit::Expl {
                match dv {
                    Val::TyCon(id, _) if Some(id) == wk.int => sizes.push((vec![var], x.to_string())),
                    Val::TyCon(id, _) if [wk.list, wk.string, wk.array].contains(&Some(id)) => {
                        sizes.push((vec![Tm::PrimApp(Prim::Len, vec![var])], format!("len {x}")))
                    }
                    _ => {}
                }
            }
            names.push(x.clone());
            ty = (*body).clone();
            k += 1;
        }
        let mut out: Vec<Measure> = sizes.clone();
        let push = |m: Measure, out: &mut Vec<Measure>| {
            if !out.iter().any(|o| o.1 == m.1) {
                out.push(m);
            }
        };
        // Guards' distances.
        for c in calls {
            let lvl = c.ob.ctx.len();
            for f in &c.ob.facts {
                let t = quote(&self.g, lvl, f);
                let mut found = Vec::new();
                comparisons(&self.g, &t, true, &mut found);
                for (a, b, strict) in found {
                    let (Some(a), Some(b)) = (reindex(&a, lvl, n, 0), reindex(&b, lvl, n, 0)) else { continue };
                    // Against zero (`0 <= n`, `x < 0`), the distance is the
                    // other side itself, or its negation.
                    let zero = |t: &Tm| matches!(t, Tm::Lit(Lit::Num(0)));
                    let mut dist = match (zero(&a), zero(&b)) {
                        (true, _) => b,
                        (_, true) => Tm::PrimApp(Prim::Neg, vec![a]),
                        _ => Tm::PrimApp(Prim::Sub, vec![b, a]),
                    };
                    if !strict && !matches!(&dist, Tm::Var(_)) {
                        dist = Tm::PrimApp(Prim::Add, vec![dist, Tm::Lit(Lit::Num(1))]);
                    }
                    // Not a constant: it must mention a parameter.
                    let mut lv = Vec::new();
                    super::free_levels_pub(&dist, n, 0, &mut lv);
                    if lv.is_empty() {
                        continue;
                    }
                    let text = crate::core::show(&self.g, &names, &dist);
                    push((vec![dist], text), &mut out);
                }
            }
        }
        // Sums of two sizes (a merge's `length xs + length ys`).
        for i in 0..sizes.len() {
            for j in i + 1..sizes.len() {
                let t = Tm::PrimApp(Prim::Add, vec![sizes[i].0[0].clone(), sizes[j].0[0].clone()]);
                push((vec![t], format!("{} + {}", sizes[i].1, sizes[j].1)), &mut out);
            }
        }
        out.truncate(10);
        out
    }
}

/// The comparisons `t` (a fact, true when `pol`) says hold: `(a, b, strict)`
/// for `a < b` (strict) or `a <= b`; through `and`, `or` (false), `not`.
fn comparisons(g: &Globals, t: &Tm, pol: bool, out: &mut Vec<(Tm, Tm, bool)>) {
    let wk = &g.well_known;
    let is_con = |t: &Tm, c: Option<ConId>| matches!(t, Tm::ConApp(k, a) if Some(*k) == c && a.is_empty());
    match t {
        Tm::PrimApp(Prim::Eq, xs) if xs.len() == 2 && (is_con(&xs[1], wk.true_con) || is_con(&xs[1], wk.false_con)) => {
            comparisons(g, &xs[0], pol == is_con(&xs[1], wk.true_con), out);
        }
        Tm::PrimApp(p @ (Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge), xs) if xs.len() == 2 => {
            let (a, b) = (xs[0].clone(), xs[1].clone());
            // As `lo < hi` or `lo <= hi`.
            let (lo, hi, strict) = match (p, pol) {
                (Prim::Lt, true) => (a, b, true),
                (Prim::Le, true) => (a, b, false),
                (Prim::Gt, true) => (b, a, true),
                (Prim::Ge, true) => (b, a, false),
                (Prim::Lt, false) => (b, a, false),
                (Prim::Le, false) => (b, a, true),
                (Prim::Gt, false) => (a, b, false),
                _ => (a, b, true),
            };
            out.push((lo, hi, strict));
        }
        Tm::Case(c, ct) if ct.lits.is_empty() && ct.default.is_none() && ct.branches.len() == 2 => {
            let br = |k: Option<ConId>| ct.branches.iter().find(|b| Some(b.0) == k && b.1 == 0).map(|b| &b.2);
            let (Some(tb), Some(fb)) = (br(wk.true_con), br(wk.false_con)) else { return };
            if pol && is_con(fb, wk.false_con) {
                // `c and tb`
                comparisons(g, c, true, out);
                comparisons(g, tb, true, out);
            } else if !pol && is_con(tb, wk.true_con) {
                // not (`c or fb`)
                comparisons(g, c, false, out);
                comparisons(g, fb, false, out);
            } else if is_con(tb, wk.false_con) && is_con(fb, wk.true_con) {
                // `not c`
                comparisons(g, c, !pol, out);
            }
        }
        _ => {}
    }
}

/// `t`, a term at level `from`, as a term at level `to` (`to <= from`), if
/// every local it mentions is below `to`.
fn reindex(t: &Tm, from: usize, to: usize, depth: usize) -> Option<Tm> {
    let go = |x: &Tm, d: usize| reindex(x, from, to, d);
    Some(match t {
        Tm::Var(i) if *i < depth => Tm::Var(*i),
        Tm::Var(i) => {
            let lvl = from.checked_sub(1 + (*i - depth))?;
            if lvl >= to {
                return None;
            }
            Tm::Var(to - 1 - lvl + depth)
        }
        Tm::App(a, b, i, m) => Tm::App(Rc::new(go(a, depth)?), Rc::new(go(b, depth)?), *i, *m),
        Tm::PrimApp(p, xs) => Tm::PrimApp(p.clone(), xs.iter().map(|x| go(x, depth)).collect::<Option<_>>()?),
        Tm::ConApp(c, xs) => Tm::ConApp(*c, xs.iter().map(|x| go(x, depth)).collect::<Option<_>>()?),
        Tm::Field(b, c, k) => Tm::Field(Rc::new(go(b, depth)?), *c, *k),
        Tm::Proj(b, k, r) => Tm::Proj(Rc::new(go(b, depth)?), *k, *r),
        Tm::Def(_) | Tm::Con(_) | Tm::TyCon(_) | Tm::Lit(_) => t.clone(),
        _ => return None,
    })
}

/// Is there a choice of one parameter per function such that every call
/// inside the group passes a strict subterm of the caller's chosen parameter
/// in the callee's chosen position?
fn structural(members: &[DefId], metas: &[FnMeta], calls: &[&CallRec]) -> bool {
    let arities: Vec<usize> = metas.iter().map(|m| m.params.len()).collect();
    if arities.contains(&0) {
        return false;
    }
    let total: usize = arities.iter().product();
    if total > 4096 {
        return false;
    }
    let mut choice = vec![0usize; members.len()];
    for k in 0..total {
        let mut r = k;
        for (i, a) in arities.iter().enumerate() {
            choice[i] = r % a;
            r /= a;
        }
        let ok = calls.iter().all(|c| {
            let fi = members.iter().position(|d| *d == c.caller).unwrap();
            let gi = members.iter().position(|d| *d == c.callee).unwrap();
            c.args.get(choice[gi]).copied().flatten() == Some(choice[fi])
        });
        if ok {
            return true;
        }
    }
    false
}
