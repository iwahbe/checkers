//! Calls with effects (§7.1, §8.3). A call given a capability or a
//! `Sched`, as an argument or inside one (a field, an element), or a call
//! of a local function that captured one, is not a function of its
//! arguments: two such calls may return different values (two lines read,
//! two new cowns). Each is wrapped in `Prim::Effect`, numbered: to the
//! prover a value of its own, known by what the callee promises of it; at
//! run time, the call.
//!
//! A function value passed to a call is looked into where it is known (a
//! lambda, a partial application, a local defined as one): what it
//! captured. A type variable, and a function parameter called, are taken
//! as having no effects: generic code is proved for every type, and the
//! call that instantiates it at a capability is a call with effects.

use super::*;

/// The types whose values carry an effect: the authority capabilities and
/// the scheduler (§8.2, §8.3), files and process handles.
const EFFECT_TYPES: &[(&str, &str)] = &[
    ("std.terminal", "Term"),
    ("std.files", "Fs"),
    ("std.files", "File"),
    ("std.system", "Env"),
    ("std.system", "Proc"),
    ("std.system", "Net"),
    ("std.system", "Clock"),
    ("std.cown", "Sched"),
    ("std.proc", "Child"),
    ("std.proc", "Killer"),
];

/// The builtins whose results are never known when compiling, though they
/// have no effects (§8.9): a test or benchmark's inputs go through them.
const NEVER_KNOWN: &[(&str, &str)] = &[("std.hint", "blackbox")];

/// A call with effects: the types of the values it is given, where its
/// function is named (`None` for a local function, which may hold anything).
pub(super) struct Effects {
    pub given: Option<Vec<Val>>,
}

impl Elab {
    /// Whether `id` is a type whose values carry an effect.
    fn is_effect_ty(&self, id: TyId) -> bool {
        let ti = &self.g.tys[id.0 as usize];
        EFFECT_TYPES.iter().any(|(m, n)| *ti.module == **m && *ti.name == **n)
    }

    /// Whether a value of type `ty` can hold a capability, a `Sched`, a file
    /// or a process handle: as itself, a part, a field or an element. Not
    /// through a function type or a type variable (see the module's
    /// comment).
    pub(super) fn holds_effect(&self, lvl: usize, ty: &Val) -> bool {
        self.can_hold(lvl, ty, &|e: &Elab, t: &Val| matches!(t, Val::TyCon(id, _) if e.is_effect_ty(*id)), false, true)
    }

    /// Whether function `d`'s signature gives it a value that holds an
    /// effect: an explicit run-time parameter of such a type (a function
    /// parameter is called by the code it runs, not given an effect). The
    /// rule of `call_effects`, for every call of `d`.
    pub(super) fn signature_effects(&self, d: DefId) -> bool {
        let mut fty = eval(&self.g, &crate::core::Env::new(), &self.g.defs[d.0 as usize].ty);
        let mut lvl = 0;
        while let Val::Pi(_, m, icit, dom, clo) = self.force(&fty) {
            if icit == Icit::Expl && m != Mult::Zero && !matches!(self.force(&dom), Val::Pi(..)) && self.holds_effect(lvl, &dom) {
                return true;
            }
            fty = apply_closure(&self.g, &clo, Val::var(lvl));
            lvl += 1;
        }
        false
    }

    /// Whether builtin `d`'s result is never known when compiling.
    pub(super) fn never_known(&self, d: DefId) -> bool {
        let info = &self.g.defs[d.0 as usize];
        NEVER_KNOWN.iter().any(|(m, n)| *info.module == **m && *info.name == **n)
    }

    /// Whether the value of `t`, a term over `cx` (a function), captured a
    /// value that holds an effect: whether a bound local it refers to holds
    /// one. Only a bound local can be one: a value refers to no other local.
    fn captures_effect(&self, cx: &Cx, t: &Tm) -> bool {
        let (refers, _) = self.term_refers(cx.lvl(), t, &|l| self.local_refers(cx, l));
        self.any_holds_effect(cx, &refers)
    }

    /// Whether one of the bound locals `ls` holds an effect.
    fn any_holds_effect(&self, cx: &Cx, ls: &[usize]) -> bool {
        ls.iter().any(|&l| self.holds_effect(cx.lvl(), &cx.ty_of(l)))
    }

    /// The bound locals, by level, outermost first, that the value of `t`,
    /// a term over the first `depth` locals, refers to: those `t` mentions,
    /// and those each local it mentions refers to (`refers`). A solved
    /// unknown is replaced by its solution first; one not yet solved refers
    /// to every bound local it is given. With whether `t` has one.
    ///
    /// Not its value's free variables: the values of the locals it refers
    /// to are not written out (in a chain of `let`s of closures, they grow
    /// with the chain), and what evaluating `t` would leave out (a branch
    /// not taken) is counted.
    fn term_refers(&self, depth: usize, t: &Tm, refers: &dyn Fn(usize) -> Rc<[usize]>) -> (Rc<[usize]>, bool) {
        let t = crate::core::zonk_metas(&self.g, depth, t);
        let mut free = std::collections::BTreeSet::new();
        free_vars(&t, 0, &mut free);
        let mut sets = free.into_iter().filter_map(|i| depth.checked_sub(1 + i)).map(refers).filter(|r| !r.is_empty());
        let all = match (sets.next(), sets.next()) {
            (None, _) => Rc::from([]),
            (Some(r), None) => r,
            (Some(a), Some(b)) => {
                let mut all: std::collections::BTreeSet<usize> = a.iter().chain(b.iter()).copied().collect();
                for r in sets {
                    all.extend(r.iter());
                }
                all.into_iter().collect()
            }
        };
        (all, super::has_meta(&t))
    }

    /// The bound locals, by level, outermost first, that local `l`'s value
    /// refers to: `l`, if it is bound; else those of the term that defined
    /// it (`term_refers`), decided once its unknowns are solved.
    fn local_refers(&self, cx: &Cx, l: usize) -> Rc<[usize]> {
        // Each local undecided that `l`'s term reaches, lowest first: one's
        // term mentions only locals before it, decided by then. A loop, not
        // recursion, however long the chain of locals.
        let mut todo = vec![l];
        let mut undecided = std::collections::BTreeSet::new();
        while let Some(m) = todo.pop() {
            let local = &cx.locals[m];
            if local.bound || local.refers.get().is_some() || !undecided.insert(m) {
                continue;
            }
            if let Some(t) = &local.def {
                let mut free = std::collections::BTreeSet::new();
                free_vars(t, 0, &mut free);
                todo.extend(free.into_iter().filter_map(|i| m.checked_sub(1 + i)));
            }
        }
        // Decided here, but with an unknown not yet solved: not kept.
        let mut fresh: HashMap<usize, Rc<[usize]>> = HashMap::new();
        let decided = |fresh: &HashMap<usize, Rc<[usize]>>, m: usize| -> Option<Rc<[usize]>> {
            let local = &cx.locals[m];
            if local.bound {
                return Some(Rc::from([m]));
            }
            local.refers.get().or_else(|| fresh.get(&m)).cloned()
        };
        for m in undecided {
            let refers = |j: usize| decided(&fresh, j).unwrap_or_else(|| self.local_refers(cx, j));
            let (r, unsolved) = match &cx.locals[m].def {
                Some(t) => self.term_refers(m, t, &refers),
                // Defined by a value alone.
                None => self.term_refers(m, &quote(&self.g, m, &cx.env[m]), &refers),
            };
            if unsolved {
                fresh.insert(m, r);
            } else {
                let _ = cx.locals[m].refers.set(r);
            }
        }
        decided(&fresh, l).expect("decided above")
    }

    /// Whether `t`, a call with all its arguments, of type `ty`, has effects.
    pub(super) fn call_effects(&self, cx: &Cx, t: &Tm, ty: &Val) -> Option<Effects> {
        if self.in_spec > 0 || self.in_proof > 0 || matches!(self.force(ty), Val::Pi(..)) {
            return None;
        }
        let (h, args) = t.spine_cloned();
        if args.is_empty() {
            return None;
        }
        let lvl = cx.lvl();
        let (mut fty, local) = match h {
            Tm::Def(d) => (eval(&self.g, &crate::core::Env::new(), &self.g.defs[d.0 as usize].ty), None),
            Tm::Var(i) => {
                let l = lvl.checked_sub(i + 1)?;
                (cx.ty_of(l), Some(l))
            }
            _ => return None,
        };
        let mut effects = local.is_some_and(|l| self.any_holds_effect(cx, &self.local_refers(cx, l)));
        let mut given = Vec::new();
        for a in &args {
            let Val::Pi(_, m, icit, dom, clo) = self.force(&fty) else { return None };
            let v = self.eval(cx, a);
            if icit == Icit::Expl && m != Mult::Zero {
                effects = effects
                    || match self.force(&dom) {
                        Val::Pi(..) => self.captures_effect(cx, a),
                        _ => self.holds_effect(lvl, &dom),
                    };
                given.push((*dom).clone());
            }
            fty = apply_closure(&self.g, &clo, v);
        }
        effects.then_some(Effects { given: local.is_none().then_some(given) })
    }

    /// `t`, a call with all its arguments, of type `ty`: wrapped in
    /// `Prim::Effect` if it has effects, with what it says of new cowns.
    pub(super) fn mark_effects(&mut self, cx: &mut Cx, t: Tm, ty: &Val) -> Tm {
        let Some(fx) = self.call_effects(cx, &t, ty) else { return t };
        self.effect_count += 1;
        let marked = Tm::PrimApp(Prim::Effect(self.effect_count), vec![t]);
        if let Some(given) = fx.given {
            let v = self.eval(cx, &marked);
            self.assume_new_cowns(cx, &v, ty, &given);
        }
        marked
    }
}
