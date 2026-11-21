//! Showing values by type (#170, §9.11). A function that shows values of
//! a type parameter (`debug`), itself or through a function it calls with
//! it, is passed that type's descriptor rather than only its layout, so
//! the runtime shows them as their type says. The requirement is closed
//! over each module's uses of generic functions, as D125 (b)'s is for
//! `==`; each type argument it reaches must be known when the program is
//! compiled: one that depends on a value known only at run time is E0293.

use super::*;
use std::collections::BTreeSet;

impl Elab {
    /// The positions of `d`'s leading binders that are types or type
    /// constructors.
    fn type_formers(&self, d: DefId) -> Vec<(usize, Name)> {
        let mut out = Vec::new();
        let mut v = eval(&self.g, &Rc::new(Vec::new()), &self.g.defs[d.0 as usize].ty);
        let mut k = 0;
        while let Val::Pi(x, _, _, dom, c) = self.force(&v) {
            if crate::core::is_type_former(&quote(&self.g, k, &dom)) {
                out.push((k, x.clone()));
            }
            v = apply_closure(&self.g, &c, Val::var(k));
            k += 1;
        }
        out
    }

    /// The type variables a descriptor of `ty` is built from (`vars`), and
    /// the variables it depends on that aren't types (`values`): what it
    /// is can only be known when the program runs.
    fn desc_vars(&self, ty: &Val, depth: usize, vars: &mut BTreeSet<usize>, values: &mut BTreeSet<usize>) {
        if depth > 32 {
            return;
        }
        match self.force(ty) {
            Val::TyCon(id, args) => {
                let params = self.g.tys[id.0 as usize].params.clone();
                for (k, a) in args.iter().enumerate() {
                    if params.get(k).is_some_and(|(_, t)| crate::core::is_type_former(t)) {
                        self.desc_vars(a, depth + 1, vars, values);
                    }
                }
            }
            Val::TupleTy(ts) => ts.iter().for_each(|t| self.desc_vars(t, depth + 1, vars, values)),
            Val::Neutral(Head::Var(l), sp) => match sp.as_slice() {
                [] => {
                    vars.insert(l);
                }
                // A class's type kept in a dictionary (#133).
                [Elim::Field(c, i)] if self.g.is_dict_type_field(*c, *i) => {}
                // A type constructor parameter applied (M25), or a type
                // computed from a value (`if b then U8 else Int`): which
                // of the two the variable is decides.
                _ => {
                    vars.insert(l);
                    for e in sp.iter() {
                        if let Elim::App(a, _) = e {
                            self.desc_vars(a, depth + 1, vars, values);
                        } else {
                            values.insert(l);
                        }
                    }
                }
            },
            _ => {}
        }
    }

    /// The type parameters of `owner` that `ty` (at level `lvl`) needs
    /// described, or the first variable it depends on that isn't one.
    fn check_described(&self, ty: &Val, owner: Option<DefId>) -> Result<Vec<usize>, usize> {
        let (mut vars, mut values) = (BTreeSet::new(), BTreeSet::new());
        self.desc_vars(ty, 0, &mut vars, &mut values);
        let params = owner.map(|d| self.type_formers(d)).unwrap_or_default();
        if let Some(l) = values.iter().next() {
            return Err(*l);
        }
        let mut out = Vec::new();
        for l in vars {
            if params.iter().any(|(k, _)| *k == l) {
                out.push(l);
            } else {
                return Err(l);
            }
        }
        Ok(out)
    }

    /// Close the requirement over this module's uses of generic functions,
    /// record it for code generation, then check every use.
    pub(super) fn resolve_descs(&mut self, insts: &[Inst]) {
        if self.g.well_known.debug.is_none() {
            // `std.string`'s `debug`, the derived `Debug` (#126): the
            // runtime's printer, a builtin.
            self.g.well_known.debug =
                self.g.defs.iter().position(|d| &*d.module == "std.string" && &*d.name == "debug" && d.body.is_none()).map(|i| DefId(i as u32));
        }
        let Some(debug) = self.g.well_known.debug else { return };
        if !self.desc_reqs.contains_key(&debug) {
            if let Some((k, name)) = self.type_formers(debug).into_iter().next() {
                self.desc_reqs.entry(debug).or_default().insert(k, EqReq { root: debug, param: name });
            }
        }
        loop {
            let mut changed = false;
            for i in insts {
                let Some(caller) = i.caller else { continue };
                let reqs: Vec<(usize, EqReq)> = match self.desc_reqs.get(&i.callee) {
                    Some(r) => r.iter().map(|(k, v)| (*k, v.clone())).collect(),
                    None => continue,
                };
                for (k, why) in reqs {
                    let Some(arg) = i.args.get(k) else { continue };
                    if let Ok(params) = self.check_described(arg, Some(caller)) {
                        let names = self.type_formers(caller);
                        let mine = self.desc_reqs.entry(caller).or_default();
                        for p in params {
                            if let std::collections::btree_map::Entry::Vacant(e) = mine.entry(p) {
                                let name = names.iter().find(|(q, _)| *q == p).map(|(_, n)| n.clone()).unwrap_or_else(|| why.param.clone());
                                e.insert(EqReq { root: why.root, param: name });
                                changed = true;
                            }
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for (d, reqs) in &self.desc_reqs {
            self.g.well_known.desc_params.insert(*d, reqs.keys().copied().collect());
        }
        for i in insts {
            let reqs: Vec<(usize, EqReq)> = match self.desc_reqs.get(&i.callee) {
                Some(r) => r.iter().map(|(k, v)| (*k, v.clone())).collect(),
                None => continue,
            };
            for (k, why) in reqs {
                let Some(arg) = i.args.get(k) else { continue };
                let Err(l) = self.check_described(arg, i.caller) else { continue };
                let callee = self.g.defs[i.callee.0 as usize].name.to_string();
                let param = self.type_formers(i.callee).into_iter().find(|(p, _)| *p == k).map(|(_, n)| n.to_string()).unwrap_or_default();
                let root = self.g.defs[why.root.0 as usize].name.to_string();
                let through = if why.root == i.callee {
                    String::new()
                } else if why.param.as_ref() == param.as_str() {
                    format!(" (through `{root}`)")
                } else {
                    format!(" (through `{root}`, as `{}`)", why.param)
                };
                let shown = show(&self.g, &i.names, &quote(&self.g, i.lvl, arg));
                let var = i.names.get(l).map(|n| n.to_string()).unwrap_or_else(|| "_".into());
                self.err(
                    Diagnostic::error(
                        "E0293",
                        format!("`{callee}` shows values of type `{param}`{through}, so `{param}` must be known when the program is compiled"),
                        i.span,
                    )
                    .with_label(format!("`{param}` is `{shown}` here, which depends on `{var}`")),
                );
            }
        }
    }
}
