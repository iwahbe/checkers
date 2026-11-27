//! A module's own functions proved on demand (§8.9): a value known at
//! compile time may need a function of the module being checked, which
//! runs only once it is proved. Its recursive group and every function it
//! reaches are proved then, in dependency order, their termination and
//! their obligations, and the proofs phase uses those proofs rather than
//! asking again.

use super::*;

/// What was proved before the proofs phase (§8.9), which that phase then
/// takes as proved.
#[derive(Default)]
pub struct Early {
    /// This module's functions (and constants) found proved: they may run.
    pub settled: HashSet<DefId>,
    /// Those found not to be (an error, an obligation not proved, or
    /// something not checked yet that can't be now): they don't run.
    pub unsettled: HashSet<DefId>,
    /// Those being proved now: they don't run yet (a call of one in its own
    /// obligations, whose value would be a fact, isn't known).
    pub proving: HashSet<DefId>,
    /// Obligations proved, by their index in `Elab::obligations`.
    pub obs: HashSet<usize>,
    /// Measure obligations proved, which termination checking adds to
    /// `Elab::obligations` only at the module's end: by where and what.
    pub measures: Vec<(Span, ObKind)>,
    /// Recursive groups whose guessed measure was proved (#641).
    pub guesses: HashSet<Vec<DefId>>,
    /// How many obligations each module had proved so.
    pub counts: HashMap<String, usize>,
}

impl Early {
    /// Was obligation `o`, at index `k`, proved already?
    pub fn proved(&self, k: usize, o: &Obligation) -> bool {
        self.obs.contains(&k) || matches!(o.kind, ObKind::Measure { .. }) && self.measures.iter().any(|(s, kind)| *s == o.span && *kind == o.kind)
    }
}

impl Elab {
    /// May `d`, of the module being checked, run at compile time? Only once
    /// it is proved: its recursive group and every function it reaches,
    /// each group proved here, dependencies first, if not already.
    pub fn settle(&self, d: DefId) -> bool {
        {
            let early = self.early.borrow();
            if early.settled.contains(&d) {
                return true;
            }
            if early.unsettled.contains(&d) || early.proving.contains(&d) {
                return false;
            }
        }
        // What `d` reaches in this module, and the calls between them.
        let mine = |x: DefId| self.g.defs.get(x.0 as usize).is_some_and(|i| *i.module == *self.cur);
        let mut nodes: Vec<DefId> = vec![d];
        let mut index: HashMap<DefId, usize> = HashMap::from([(d, 0)]);
        let mut edges: Vec<Vec<usize>> = Vec::new();
        let mut k = 0;
        while k < nodes.len() {
            let x = nodes[k];
            let mut used = Vec::new();
            if let Some(b) = &self.g.defs[x.0 as usize].body {
                crate::core::defs_in(b, &mut used);
            }
            let mut out = Vec::new();
            for u in used.into_iter().filter(|u| mine(*u)) {
                let n = *index.entry(u).or_insert_with(|| {
                    nodes.push(u);
                    nodes.len() - 1
                });
                out.push(n);
            }
            edges.push(out);
            k += 1;
        }
        for scc in super::order::sccs(&edges) {
            let members: Vec<DefId> = scc.iter().map(|&i| nodes[i]).collect();
            if members.iter().all(|m| self.early.borrow().settled.contains(m)) {
                continue;
            }
            if members.iter().any(|m| self.early.borrow().proving.contains(m)) {
                return false;
            }
            self.early.borrow_mut().proving.extend(members.iter().copied());
            let ok = members.iter().all(|m| !self.early.borrow().unsettled.contains(m)) && self.settle_group(&members);
            let mut early = self.early.borrow_mut();
            for m in &members {
                early.proving.remove(m);
            }
            if ok {
                early.settled.extend(members);
            } else {
                // Nothing that reaches it runs either.
                early.unsettled.extend(members);
                early.unsettled.insert(d);
                return false;
            }
        }
        true
    }

    /// Prove one recursive group of the module's functions, whose callees
    /// in the module are proved: false if it can't be, now.
    fn settle_group(&self, members: &[DefId]) -> bool {
        let set: HashSet<DefId> = members.iter().copied().collect();
        // Each one checked already, a function or a constant: not a
        // constant whose value needs itself, nor one waiting for its body.
        for m in members {
            let info = &self.g.defs[m.0 as usize];
            let is_fn = self.fn_meta.get(m).is_some_and(|f| f.is_fn);
            if info.body.is_none() || ((members.len() > 1 || self.calls_itself(*m)) && !is_fn) {
                return false;
            }
        }
        // Where they are: no error there, and nothing waiting for the
        // module's end (dictionaries settled only once every body is checked).
        let spans: Vec<Span> = self
            .decl_spans
            .get(&self.cur)
            .map(|ds| ds.iter().filter(|(_, s)| matches!(s, Some(Sym::Def(x)) if set.contains(x))).map(|(sp, _)| *sp).collect())
            .unwrap_or_default();
        let inside = |s: Span| spans.iter().any(|d| d.start <= s.start && s.end <= d.end);
        if self.diags.iter().any(|(m, d)| *m == self.cur && d.is_error() && inside(d.span)) {
            return false;
        }
        let owned = |o: &Option<DefId>, s: Span| o.is_some_and(|o| set.contains(&o)) || inside(s);
        let waiting = self.pending_class_pres.iter().any(|p| owned(&p.owner, p.span))
            || self.class_calls.iter().any(|p| owned(&p.owner, p.span))
            || self.class_local_calls.iter().any(|(_, p)| owned(&p.owner, p.span))
            || self.alias_dicts.iter().any(|a| owned(&a.owner, a.span))
            || self.class_value_uses.iter().any(|u| inside(u.2))
            || self.waiting.iter().any(|w| inside(w.3));
        if waiting {
            return false;
        }
        // Termination, as the module's end will check it.
        let fns: Vec<DefId> = members.iter().copied().filter(|m| self.module_fns.contains(m)).collect();
        let mut guesses = Vec::new();
        let mut measures: Vec<&Obligation> = Vec::new();
        if !fns.is_empty() {
            self.decide_memberships();
            let held = self.promises_so_far();
            let calls: Vec<CallRec> = self.calls.iter().filter(|c| set.contains(&c.caller)).cloned().collect();
            let rec_calls: Vec<termination::RecCall> = self.rec_calls.iter().filter(|c| set.contains(&c.caller)).cloned().collect();
            let v = self.termination_verdict(&fns, calls, &held, &rec_calls);
            if !v.errors.is_empty() {
                return false;
            }
            for total in &v.measured {
                measures.extend(self.measure_obs.iter().filter(|(a, b, _)| total.contains(a) && total.contains(b)).map(|(_, _, o)| o));
            }
            guesses = v.guesses;
        }
        // Their obligations, those of their signatures too.
        let early = self.early.borrow();
        let (ks, mut obs): (Vec<usize>, Vec<&Obligation>) = self
            .obligations
            .iter()
            .enumerate()
            .filter(|(k, o)| o.module == self.cur && owned(&o.owner, o.span) && !early.obs.contains(k))
            .unzip();
        drop(early);
        let n = obs.len();
        obs.extend(measures.iter().copied());
        let gs: Vec<&termination::GuessGroup> = guesses.iter().collect();
        let Some(proved) = crate::verify::prove_now(self, &self.cur, &obs, &gs) else { return false };
        let mut early = self.early.borrow_mut();
        early.obs.extend(ks);
        early.measures.extend(obs[n..].iter().map(|o| (o.span, o.kind.clone())));
        early.guesses.extend(guesses.into_iter().map(|g| g.members));
        *early.counts.entry(self.cur.clone()).or_default() += proved;
        true
    }

    /// Does constant or function `d` use itself?
    fn calls_itself(&self, d: DefId) -> bool {
        let mut used = Vec::new();
        if let Some(b) = &self.g.defs[d.0 as usize].body {
            crate::core::defs_in(b, &mut used);
        }
        used.contains(&d)
    }
}
