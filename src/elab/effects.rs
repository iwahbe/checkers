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
        self.can_hold(lvl, ty, &|e: &Elab, t: &Val| matches!(t, Val::TyCon(id, _) if e.is_effect_ty(*id)), false, 0, &mut Vec::new())
    }

    /// Whether function value `v` captured a value that holds an effect.
    fn captures_effect(&self, cx: &Cx, v: &Val) -> bool {
        let lvl = cx.lvl();
        let t = quote(&self.g, lvl, v);
        let mut free = std::collections::BTreeSet::new();
        free_vars(&t, 0, &mut free);
        free.into_iter().any(|i| i < lvl && self.holds_effect(lvl, &cx.ty_of(lvl - 1 - i)))
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
            Tm::Def(d) => (eval(&self.g, &Rc::new(Vec::new()), &self.g.defs[d.0 as usize].ty), false),
            Tm::Var(i) => {
                let l = lvl.checked_sub(i + 1)?;
                (cx.ty_of(l), true)
            }
            _ => return None,
        };
        let mut effects = local && self.captures_effect(cx, &self.eval(cx, h));
        let mut given = Vec::new();
        for a in &args {
            let Val::Pi(_, m, icit, dom, clo) = self.force(&fty) else { return None };
            let v = self.eval(cx, a);
            if icit == Icit::Expl && m != Mult::Zero {
                effects = effects
                    || match self.force(&dom) {
                        Val::Pi(..) => self.captures_effect(cx, &v),
                        _ => self.holds_effect(lvl, &dom),
                    };
                given.push((*dom).clone());
            }
            fty = apply_closure(&self.g, &clo, v);
        }
        effects.then_some(Effects { given: (!local).then_some(given) })
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
