//! Termination (§5.3): structural recursion, `decreasing` measures, `partial`,
//! and measures guessed for recursion that is none of these (#641).

use super::*;

/// A call between two functions of the module, neither with a measure: what
/// a guessed measure must make smaller (#641).
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

/// What checking the termination of a module's functions finds
/// (`termination_verdict`), before it is applied.
#[derive(Default)]
pub struct Verdict {
    pub errors: Vec<Diagnostic>,
    /// The total members of each group recursing by `decreasing` measures,
    /// whose calls' measure obligations are to be proved.
    pub measured: Vec<Vec<DefId>>,
    /// The groups whose measure is guessed (#641).
    pub guesses: Vec<GuessGroup>,
}

/// A recursive group whose measure is guessed in the proofs phase (#641).
#[derive(Clone)]
pub struct GuessGroup {
    pub module: String,
    pub members: Vec<DefId>,
    /// Each member's candidates, in the order they are tried.
    pub candidates: Vec<Vec<Measure>>,
    pub calls: Vec<RecCall>,
    /// The recursive calls to report E0301 at, best first: those of a
    /// cycle that isn't structurally smaller, losing its parameter first
    /// (#124).
    pub prefer: Vec<Span>,
}

impl Elab {
    /// A call that may be recursion with no measure written (#641).
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

    /// The promises the module's function bodies make (#102): explicit
    /// parameter `k` of `f` is a function called only with strict parts of
    /// parameter `j` if every use of `k` in `f`'s body is such a call, or
    /// passes `k` to a function that promises it. The largest set of
    /// promises that holds, as functions may pass their parameters to each
    /// other (or themselves) recursively.
    fn body_promises(&mut self) -> HashSet<ElemAlt> {
        let fns: Vec<DefId> = std::mem::take(&mut self.body_fns);
        let uses = std::mem::take(&mut self.param_uses);
        let held = self.promises(&fns, &uses);
        for f in &fns {
            let mut ps: Vec<(usize, usize)> = held.iter().filter(|x| x.0 == *f).map(|x| (x.1, x.2)).collect();
            ps.sort();
            self.body_elems.insert(*f, ps);
        }
        held
    }

    /// The promises that hold of the bodies checked so far, which the
    /// module's end decides for all its bodies (`body_promises`).
    pub(super) fn promises_so_far(&self) -> HashSet<ElemAlt> {
        self.promises(&self.body_fns, &self.param_uses)
    }

    /// The promises of `fns`' bodies that hold (`body_promises`), from the
    /// uses of their parameters.
    fn promises(&self, fns: &[DefId], uses: &HashMap<(DefId, usize), Vec<ParamUse>>) -> HashSet<ElemAlt> {
        let mut held: HashSet<ElemAlt> = HashSet::new();
        for f in fns {
            let n = self.fn_meta.get(f).map_or(0, |m| m.params.len());
            for k in 0..n {
                for j in (0..n).filter(|j| *j != k) {
                    held.insert((*f, k, j));
                }
            }
        }
        let empty = Vec::new();
        loop {
            let failed: Vec<ElemAlt> = held
                .iter()
                .copied()
                .filter(|&(f, k, j)| {
                    let us = uses.get(&(f, k)).unwrap_or(&empty);
                    !us.iter().all(|u| u.iter().any(|&(p, c)| p == j && self.cond_holds(c, &held)))
                })
                .collect();
            if failed.is_empty() {
                break;
            }
            for x in failed {
                held.remove(&x);
            }
        }
        held
    }

    /// Whether condition `c` holds: one of its promises does (#102), in
    /// the callee's signature (a precondition that is a membership), or
    /// read from its body (this module's, in `held`, or a `transparent`
    /// function's of another module).
    fn cond_holds(&self, c: Option<u32>, held: &HashSet<ElemAlt>) -> bool {
        let Some(c) = c else { return true };
        self.elem_conds[c as usize].iter().any(|&(d, k, j)| {
            self.specs.get(&d).is_some_and(|s| {
                s.elems.iter().any(|e| e.k == k && e.j == j && self.memberships.borrow().get(&(e.pred, e.c, e.s)) == Some(&true))
            }) || held.contains(&(d, k, j))
                || (*self.g.defs[d.0 as usize].module != *self.cur
                    && self.transparent.contains(&d)
                    && self.body_elems.get(&d).is_some_and(|ps| ps.contains(&(k, j))))
        })
    }

    /// Why condition `cond`, made where `rec` is passed to a function, fails
    /// (#102): E0301's help.
    fn unkept_help(&self, cond: u32, rec: DefId) -> Option<String> {
        let (head, arg, j) = self.elem_cond_at.get(&cond)?;
        let &(d, k, _) = self.elem_conds[cond as usize].first()?;
        let j = *j;
        let rec = self.fn_meta.get(&rec).map(|m| m.name.clone()).unwrap_or_default();
        let params = self.fn_meta.get(&d).map(|m| m.params.clone()).unwrap_or_default();
        let (pk, pj) = (params.get(k).map(|p| p.0.clone())?, params.get(j).map(|p| p.0.clone())?);
        let promise = self.specs.get(&d).and_then(|s| s.elems.iter().find(|e| e.k == k && e.j == j).copied());
        let why = match promise {
            Some(e) => {
                let pred = self.g.defs[e.pred.0 as usize].name.to_string();
                if self.body_visible(e.pred) && !self.g.defs[e.pred.0 as usize].opaque {
                    format!(
                        "`{pred}`, in its precondition on `{pk}`, isn't a membership: it must be true only of something equal to a part of `{pj}`"
                    )
                } else {
                    format!("`{pred}`, in its precondition on `{pk}`, is sealed, so it can't be seen to be a membership")
                }
            }
            None if self.body_visible(d) => format!(
                "it uses `{pk}` other than by calling it with a part of `{pj}` or passing it on to a function that does"
            ),
            None => format!(
                "its body is sealed; its signature can promise it with a precondition on `{pk}` such as `{pk}~(x~a -> b, list.contains {pj} x)`"
            ),
        };
        Some(format!("`{head}` isn't known to call `{rec}` only with parts of `{arg}`: {why}"))
    }

    /// Decide, for each signature promise a condition names, whether its
    /// predicate is a membership (#102).
    pub(super) fn decide_memberships(&self) {
        // Whether a body is visible depends on the module checked.
        self.memberships.borrow_mut().clear();
        let mut todo = Vec::new();
        for alts in &self.elem_conds {
            for &(d, k, j) in alts {
                for e in self.specs.get(&d).map(|s| s.elems.as_slice()).unwrap_or(&[]) {
                    if e.k == k && e.j == j {
                        todo.push((e.pred, e.c, e.s));
                    }
                }
            }
        }
        for key in todo {
            if !self.memberships.borrow().contains_key(&key) {
                let mut visiting = HashSet::new();
                let m = self.is_membership(key, &mut visiting);
                self.memberships.borrow_mut().insert(key, m);
            }
        }
    }

    /// Whether predicate `pred` is true only where its explicit argument
    /// `s` equals (`==`, which compares structure) a strict part of its
    /// explicit argument `c`, as its body shows (#102): its body must be
    /// visible, as for proofs. A recursive use of a predicate being decided
    /// is assumed to be one: it is total, so this is an induction on its
    /// recursion.
    fn is_membership(&self, key: (DefId, usize, usize), visiting: &mut HashSet<(DefId, usize, usize)>) -> bool {
        if let Some(m) = self.memberships.borrow().get(&key).copied() {
            return m;
        }
        if !visiting.insert(key) {
            return true;
        }
        let (pred, c, s) = key;
        let info = &self.g.defs[pred.0 as usize];
        let partial = self.fn_meta.get(&pred).is_some_and(|m| m.partial);
        let Some(body) = info.body.clone().filter(|_| !info.opaque && !partial && self.body_visible(pred)) else {
            return false;
        };
        let mut ctx = Vec::new();
        let mut t = &body;
        let mut explicit = 0;
        while let Tm::Lam(_, _, i, b) = t {
            ctx.push(match i {
                Icit::Impl => Kind::Other,
                Icit::Expl => {
                    explicit += 1;
                    if explicit - 1 == c {
                        Kind::Container
                    } else if explicit - 1 == s {
                        Kind::Subject
                    } else {
                        Kind::Other
                    }
                }
            });
            t = b;
        }
        let t = t.clone();
        self.only_if_member(&t, &mut ctx, visiting)
    }

    /// Whether `t`, a `Bool`, is `True` only where the subject equals a
    /// strict part of the container (#102).
    fn only_if_member(&self, t: &Tm, ctx: &mut Vec<Kind>, visiting: &mut HashSet<(DefId, usize, usize)>) -> bool {
        let wk = &self.g.well_known;
        let (tc, fc) = (wk.true_con, wk.false_con);
        match t {
            Tm::ConApp(con, args) => args.is_empty() && Some(*con) == fc,
            Tm::Con(con) => Some(*con) == fc,
            Tm::PrimApp(Prim::Eq, xs) if xs.len() == 2 => {
                let (a, b) = (kind_of(&xs[0], ctx), kind_of(&xs[1], ctx));
                matches!((a, b), (Kind::Part, Kind::Subject) | (Kind::Subject, Kind::Part))
            }
            Tm::Let(_, _, _, v, b) => {
                let k = kind_of(v, ctx);
                ctx.push(k);
                let r = self.only_if_member(b, ctx, visiting);
                ctx.pop();
                r
            }
            Tm::Case(scrut, ct) => {
                let field = match kind_of(scrut, ctx) {
                    Kind::Container | Kind::Part => Kind::Part,
                    _ => Kind::Other,
                };
                let ct = ct.clone();
                for (con, n, b) in &ct.branches {
                    let before = ctx.len();
                    ctx.extend(std::iter::repeat_n(field, *n));
                    let mut ok = self.only_if_member(b, ctx, visiting);
                    ctx.truncate(before);
                    // `if c then b else …`: `c` true too.
                    if !ok && *n == 0 && Some(*con) == tc {
                        ok = self.only_if_member(scrut, ctx, visiting);
                    }
                    if !ok {
                        return false;
                    }
                }
                ct.lits.iter().all(|(_, b)| self.only_if_member(b, ctx, visiting))
                    && ct.default.as_ref().is_none_or(|b| self.only_if_member(b, ctx, visiting))
            }
            Tm::App(..) => {
                let (head, args) = t.spine();
                let Tm::Def(d) = head else { return false };
                let d = *d;
                let expl: Vec<Kind> = args
                    .iter()
                    .zip(app_icits(t))
                    .filter(|(_, i)| *i == Icit::Expl)
                    .map(|(a, _)| kind_of(a, ctx.as_slice()))
                    .collect();
                for (s2, ks) in expl.iter().enumerate() {
                    if *ks != Kind::Subject {
                        continue;
                    }
                    for (c2, kc) in expl.iter().enumerate() {
                        if matches!(kc, Kind::Container | Kind::Part) && self.is_membership((d, c2, s2), visiting) {
                            return true;
                        }
                    }
                }
                false
            }
            _ => false,
        }
    }

    pub fn check_termination(&mut self) {
        self.decide_memberships();
        let held = self.body_promises();
        let fns: Vec<DefId> = std::mem::take(&mut self.module_fns);
        let calls: Vec<CallRec> = std::mem::take(&mut self.calls);
        let rec_calls: Vec<RecCall> = std::mem::take(&mut self.rec_calls);
        let v = self.termination_verdict(&fns, calls, &held, &rec_calls);
        self.elem_conds.clear();
        self.elem_cond_at.clear();
        for d in v.errors {
            self.err(d);
        }
        // `decreasing` measures are proof obligations at each call in the group (§5.3).
        for total in &v.measured {
            for (caller, callee, ob) in std::mem::take(&mut self.measure_obs) {
                if total.contains(&caller) && total.contains(&callee) {
                    self.obligations.push(ob);
                } else {
                    self.measure_obs.push((caller, callee, ob));
                }
            }
        }
        // No measure written: one is guessed, and proved, later (#641).
        for g in v.guesses {
            self.guessed.extend(g.members.iter().copied());
            self.guess_groups.push(g);
        }
    }

    /// The termination of `fns` (§5.3), whose calls are `calls`, with the
    /// promises `held` their bodies make (#102): what checking it reports
    /// and needs proved, without applying it, so it can also be asked of a
    /// module's functions before the module is checked (§8.9: they are
    /// proved on demand).
    pub fn termination_verdict(&self, fns: &[DefId], mut calls: Vec<CallRec>, held: &HashSet<ElemAlt>, rec_calls: &[RecCall]) -> Verdict {
        let mut v = Verdict::default();
        // Parts that hold only if a promise does (#102).
        let mut unkept: HashMap<Span, String> = HashMap::new();
        for c in &mut calls {
            for &(i, cond) in &c.conds {
                if !self.cond_holds(Some(cond), held) {
                    c.args[i] = None;
                    if let Some(help) = self.unkept_help(cond, c.callee) {
                        unkept.entry(c.span).or_insert(help);
                    }
                }
            }
        }
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
                v.errors.push(
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
                v.measured.push(total.clone());
                // A recursive use that isn't a full call can't have its measure checked.
                for c in calls.iter().filter(|c| total.contains(&c.caller) && members.contains(&c.callee)) {
                    if !self.saturated_heads.contains(&c.span) {
                        let name = self.fn_meta.get(&c.callee).map(|m| m.name.clone()).unwrap_or_default();
                        v.errors.push(
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
            let cycle = match size_change(&members, &metas, &inner) {
                Ok(()) => continue,
                Err(cycle) => cycle,
            };
            // Recursion through an instance's dictionary (#615): a use of
            // the class's function at the instance's own type.
            if let Some(c) = inner.iter().find(|c| self.dict_defs.contains(&c.callee) && !self.dict_defs.contains(&c.caller)) {
                let inst = self.g.defs[c.callee.0 as usize].name.to_string();
                let caller = self.fn_meta.get(&c.caller).map(|m| m.name.clone()).unwrap_or_default();
                let own = caller.rsplit('.').next().unwrap_or("").to_string();
                v.errors.push(
                    Diagnostic::error("E0301", format!("`{caller}` uses `instance {inst}` itself, so it can't be shown to terminate"), c.span)
                        .with_label("the class's function at this instance's own type")
                        .with_help(format!("inside the instance, call its own `{own}` (on a smaller part of a parameter), which is checked like any recursion")),
                );
                continue;
            }
            // Report at a call of a cycle that isn't smaller (#109), made by a
            // function without `decreasing`: one passed to a function that
            // isn't known to call it only with parts first (#102), then one
            // that passes on no parameter and no part of one (where the cycle
            // loses what it was recursing on, #124), then one that passes no
            // strict part. A call passing a parameter on unchanged keeps it.
            let unmarked = |c: &CallRec| {
                let k = members.iter().position(|d| *d == c.caller).unwrap();
                !metas[k].partial && !metas[k].decreasing
            };
            let rank = |c: &CallRec| {
                if unkept.contains_key(&c.span) {
                    0
                } else if c.args.iter().chain(&c.same).all(Option::is_none) {
                    1
                } else if c.args.iter().all(Option::is_none) {
                    2
                } else {
                    3
                }
            };
            let in_cycle: Vec<&CallRec> = if cycle.is_empty() { inner.clone() } else { cycle.iter().map(|&i| inner[i]).collect() };
            let mut prefer: Vec<&CallRec> = in_cycle.iter().copied().filter(|c| unmarked(c)).collect();
            prefer.sort_by_key(|c| rank(c));
            for c in inner.iter().copied() {
                if unmarked(c) && !prefer.iter().any(|x| std::ptr::eq(*x, c)) {
                    prefer.push(c);
                }
            }
            // No measure written: one is guessed, and proved, later (#641).
            let spans: Vec<Span> = prefer.iter().map(|c| c.span).collect();
            if let Some(g) = self.guess_measure(&members, &metas, &inner, rec_calls, spans) {
                v.guesses.push(g);
                continue;
            }
            let bad = prefer.first().copied();
            if let Some(c) = bad {
                let k = members.iter().position(|d| *d == c.caller).unwrap();
                let name = metas[k].name.clone();
                let name_of = |d: DefId| metas[members.iter().position(|m| *m == d).unwrap()].name.clone();
                // The cycle, from the call reported: `a` → `b` → `a`.
                let at = in_cycle.iter().position(|x| std::ptr::eq(*x, c)).unwrap_or(0);
                let mut turn: Vec<&CallRec> = in_cycle[at..].iter().chain(&in_cycle[..at]).copied().collect();
                // One call, repeated: it is the cycle.
                if turn.iter().all(|x| std::ptr::eq(*x, c)) {
                    turn.truncate(1);
                }
                let mut route: Vec<String> = turn.iter().map(|x| format!("`{}`", name_of(x.caller))).collect();
                route.push(format!("`{name}`"));
                let file = self.sources.get(&self.cur);
                let line = |sp: Span| file.map_or(0, |f| f.line_col(sp.start).0);
                let note = (!cycle.is_empty() && turn.len() > 1).then(|| {
                    let steps: Vec<String> =
                        turn.iter().map(|x| format!("`{}` calls `{}` on line {}", name_of(x.caller), name_of(x.callee), line(x.span))).collect();
                    format!("the cycle: {}", steps.join(", then "))
                });
                let msg = if members.len() == 1 && turn.len() <= 1 {
                    format!("cannot show that `{name}` terminates: no argument gets structurally smaller in this recursive call")
                } else if members.len() == 1 {
                    format!("cannot show that `{name}` terminates: no argument gets structurally smaller over these recursive calls in turn")
                } else if cycle.is_empty() {
                    let names: Vec<String> = metas.iter().map(|m| format!("`{}`", m.name)).collect();
                    format!("cannot show that {} terminate: they call each other, and no argument gets structurally smaller", names.join(", "))
                } else {
                    let names: Vec<String> = metas.iter().map(|m| format!("`{}`", m.name)).collect();
                    format!(
                        "cannot show that {} terminate: they call each other, and no argument gets structurally smaller around {}",
                        names.join(", "),
                        route.join(" → ")
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
                let help = unkept.get(&c.span).cloned().unwrap_or(help);
                let mut d = Diagnostic::error("E0301", msg, c.span).with_label(label);
                if let Some(note) = note {
                    d = d.with_note(note);
                }
                v.errors.push(d.with_help(help));
            }
        }
        v
    }
}

impl Elab {
    /// Set up guessing a measure for a recursive group with none written
    /// (#641): every member a total function, every recursive call a full
    /// call, and candidates for each. False if it can't be.
    fn guess_measure(&self, members: &[DefId], metas: &[FnMeta], inner: &[&CallRec], rec_calls: &[RecCall], prefer: Vec<Span>) -> Option<GuessGroup> {
        if metas.iter().any(|m| m.partial || m.decreasing) {
            return None;
        }
        let calls: Vec<RecCall> =
            rec_calls.iter().filter(|c| members.contains(&c.caller) && members.contains(&c.callee)).cloned().collect();
        // Each recursive call must be one we can compare measures at.
        if inner.iter().any(|c| !calls.iter().any(|r| r.ob.span == c.span || r.ob.span.start <= c.span.start && c.span.end <= r.ob.span.end)) {
            return None;
        }
        let mut candidates = Vec::new();
        for d in members {
            let own: Vec<&RecCall> = calls.iter().filter(|c| c.caller == *d).collect();
            let cs = self.measure_candidates(*d, &own);
            if cs.is_empty() {
                return None;
            }
            candidates.push(cs);
        }
        Some(GuessGroup { module: self.cur.clone(), members: members.to_vec(), candidates, calls, prefer })
    }

    /// The measures to try for `d` (#641 a): its parameters' sizes, the
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
        while let Tm::Pi(x, _, icit, dom, body, _) = ty.clone() {
            if k >= n {
                break;
            }
            let env: Env = (0..k).map(Val::var).collect::<crate::core::Env>();
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
        // `Seq.size` of a parameter taken apart by sequence patterns (§9.8).
        for (t, lvl, text) in self.seq_sizes.get(&d).into_iter().flatten() {
            let t = crate::core::zonk_metas(&self.g, *lvl, t);
            if let Some(t) = reindex(&t, *lvl, n, 0) {
                if !sizes.iter().any(|s| s.1 == *text) {
                    sizes.push((vec![t], text.clone()));
                }
            }
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

/// How an argument relates to a parameter of the caller (#109).
const NONE: u8 = 0;
const SAME: u8 = 1;
const SMALLER: u8 = 2;

/// A size-change graph (#109): from the caller's parameters to the
/// callee's, `rel[i * to_arity + j]` how the callee's parameter `j` relates
/// to the caller's parameter `i`, made by the calls `path` in turn.
#[derive(Clone)]
struct Graph {
    from: usize,
    to: usize,
    rel: Vec<u8>,
    path: Vec<usize>,
}

/// More than this many graphs and the group is refused, as not shown to
/// terminate.
const MAX_GRAPHS: usize = 20_000;

/// Size-change termination (#109; Lee, Jones and Ben-Amram, POPL 2001).
/// Each call relates each of the callee's parameters to the caller's: a
/// strict part of one (`<`), one itself (`=`), or neither. The group
/// terminates if every cycle of calls, composed, makes some parameter
/// strictly smaller: every composed graph from a function to itself that is
/// idempotent has a `<` from a parameter to itself. Otherwise, the calls
/// (indices into `calls`) of a cycle that isn't smaller, or none if there
/// were too many graphs to tell.
fn size_change(members: &[DefId], metas: &[FnMeta], calls: &[&CallRec]) -> Result<(), Vec<usize>> {
    let arity: Vec<usize> = metas.iter().map(|m| m.params.len()).collect();
    let pos = |d: DefId| members.iter().position(|m| *m == d).unwrap();
    let base: Vec<Graph> = calls
        .iter()
        .enumerate()
        .map(|(k, c)| {
            let (from, to) = (pos(c.caller), pos(c.callee));
            let (af, at) = (arity[from], arity[to]);
            let mut rel = vec![NONE; af * at];
            for j in 0..at {
                if let Some(i) = c.args.get(j).copied().flatten().filter(|i| *i < af) {
                    rel[i * at + j] = SMALLER;
                } else if let Some(i) = c.same.get(j).copied().flatten().filter(|i| *i < af) {
                    rel[i * at + j] = SAME;
                }
            }
            Graph { from, to, rel, path: vec![k] }
        })
        .collect();
    let compose = |g: &Graph, h: &Graph| -> Vec<u8> {
        let (a, b, c) = (arity[g.from], arity[g.to], arity[h.to]);
        let mut rel = vec![NONE; a * c];
        for i in 0..a {
            for j in 0..b {
                let x = g.rel[i * b + j];
                if x == NONE {
                    continue;
                }
                for k in 0..c {
                    let y = h.rel[j * c + k];
                    if y != NONE {
                        let r = if x == SMALLER || y == SMALLER { SMALLER } else { SAME };
                        rel[i * c + k] = rel[i * c + k].max(r);
                    }
                }
            }
        }
        rel
    };
    // Every composition of calls, breadth first, so a cycle reported is a
    // short one.
    let mut seen: HashSet<(usize, usize, Vec<u8>)> = HashSet::new();
    let mut all: Vec<Graph> = Vec::new();
    for g in &base {
        if seen.insert((g.from, g.to, g.rel.clone())) {
            all.push(g.clone());
        }
    }
    let mut next = 0;
    while next < all.len() {
        if all.len() > MAX_GRAPHS {
            return Err(Vec::new());
        }
        let g = all[next].clone();
        next += 1;
        for h in base.iter().filter(|h| h.from == g.to) {
            let rel = compose(&g, h);
            if seen.insert((g.from, h.to, rel.clone())) {
                let mut path = g.path.clone();
                path.extend(&h.path);
                all.push(Graph { from: g.from, to: h.to, rel, path });
            }
        }
    }
    for g in all.iter().filter(|g| g.from == g.to) {
        let a = arity[g.from];
        let idempotent = compose(g, g) == g.rel;
        if idempotent && !(0..a).any(|i| g.rel[i * a + i] == SMALLER) {
            return Err(g.path.clone());
        }
    }
    Ok(())
}

/// What a local of a predicate being decided is (#102).
#[derive(Clone, Copy, PartialEq, Debug)]
enum Kind {
    Container,
    Part,
    Subject,
    Other,
}

/// `t`'s kind: a local's, or a field of the container or of a part.
fn kind_of(t: &Tm, ctx: &[Kind]) -> Kind {
    match t {
        Tm::Var(i) => ctx.len().checked_sub(i + 1).map_or(Kind::Other, |l| ctx[l]),
        Tm::Field(a, _, _) | Tm::Proj(a, _, _) => match kind_of(a, ctx) {
            Kind::Container | Kind::Part => Kind::Part,
            _ => Kind::Other,
        },
        _ => Kind::Other,
    }
}

/// The plicity of each argument of an application, outermost last.
fn app_icits(t: &Tm) -> Vec<Icit> {
    let mut out = Vec::new();
    let mut h = t;
    while let Tm::App(f, _, i, _) = h {
        out.push(*i);
        h = f;
    }
    out.reverse();
    out
}
