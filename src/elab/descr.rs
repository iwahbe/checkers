//! Showing values by type (#170, §9.11). A function that shows values of
//! a type parameter (`debug`), itself or through a function it calls with
//! it, is passed that type's descriptor rather than only its layout, so
//! the runtime shows them as their type says. The requirement is closed
//! over each module's uses of generic functions, as #614 (b)'s is for
//! `==`; each type argument it reaches must be known when the program is
//! compiled: one that depends on a value known only at run time is E0293.

use super::*;
use std::collections::BTreeSet;

/// Why a type can't be described when the program is compiled.
enum Why {
    /// It depends on this variable, which isn't a type parameter.
    Var(usize),
    /// It holds a field (type, constructor, field) whose type is computed
    /// from something not kept when the program runs (at this level).
    NotKept(TyId, ConId, usize, usize),
}

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
    fn desc_vars(&self, ty: &Val, depth: usize, lvl: usize, vars: &mut BTreeSet<usize>, values: &mut BTreeSet<usize>) {
        if depth > 32 {
            return;
        }
        match self.force(ty) {
            Val::TyCon(id, args) => {
                let params = self.g.tys[id.0 as usize].params.clone();
                let needed = crate::core::value_params_needed(&self.g, id);
                for (k, a) in args.iter().enumerate() {
                    if params.get(k).is_some_and(|(_, t)| crate::core::is_type_former(t)) {
                        self.desc_vars(a, depth + 1, lvl, vars, values);
                    } else if needed.contains(&k) {
                        // A value the type's fields' types are computed
                        // from: in the descriptor, so known when compiled.
                        let mut free = BTreeSet::new();
                        crate::core::free_vars(&quote(&self.g, lvl, a), 0, &mut free);
                        values.extend(free.into_iter().map(|i| lvl - 1 - i));
                    }
                }
            }
            Val::TupleTy(ts) => ts.iter().for_each(|t| self.desc_vars(t, depth + 1, lvl, vars, values)),
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
                            self.desc_vars(a, depth + 1, lvl, vars, values);
                        } else {
                            values.insert(l);
                        }
                    }
                }
            },
            _ => {}
        }
    }

    /// A field of `id`'s, or of a type its fields hold, whose type is
    /// computed from something not kept when the program runs: its type,
    /// constructor, field, and that something's level (the type's
    /// parameters, then the fields).
    fn not_kept(&self, id: TyId, seen: &mut BTreeSet<u32>) -> Option<(TyId, ConId, usize, usize)> {
        if !seen.insert(id.0) {
            return None;
        }
        for c in self.g.tys[id.0 as usize].ctors.clone() {
            let ci = &self.g.cons[c.0 as usize];
            let np = self.g.arity_ty(id);
            for k in 0..ci.fields.len() {
                if !self.g.is_runtime_field(c, k) || ci.fields[k].2 != Icit::Expl {
                    continue;
                }
                if let crate::core::FieldType::NotKept(l) = crate::core::field_type(&self.g, c, k) {
                    return Some((id, c, k, l));
                }
                let env = Rc::new((0..np + k).map(Val::var).collect::<Vec<_>>());
                let mut found = None;
                self.each_tycon(&eval(&self.g, &env, &ci.fields[k].3), 0, &mut |t| {
                    if found.is_none() {
                        found = self.not_kept(t, seen);
                    }
                });
                if found.is_some() {
                    return found;
                }
            }
        }
        None
    }

    /// `f` on each type constructor `ty` applies.
    fn each_tycon(&self, ty: &Val, depth: usize, f: &mut dyn FnMut(TyId)) {
        if depth > 32 {
            return;
        }
        match self.force(ty) {
            Val::TyCon(id, args) => {
                f(id);
                args.iter().for_each(|a| self.each_tycon(a, depth + 1, f));
            }
            Val::TupleTy(ts) => ts.iter().for_each(|t| self.each_tycon(t, depth + 1, f)),
            _ => {}
        }
    }

    /// The type parameters of `owner` that `ty` (at level `lvl`) needs
    /// described, or why it can't be described.
    fn check_described(&self, ty: &Val, lvl: usize, owner: Option<DefId>) -> Result<Vec<usize>, Why> {
        let (mut vars, mut values) = (BTreeSet::new(), BTreeSet::new());
        self.desc_vars(ty, 0, lvl, &mut vars, &mut values);
        let params = owner.map(|d| self.type_formers(d)).unwrap_or_default();
        if let Some(l) = values.iter().next() {
            return Err(Why::Var(*l));
        }
        let mut seen = BTreeSet::new();
        let mut found = None;
        self.each_tycon(ty, 0, &mut |t| {
            if found.is_none() {
                found = self.not_kept(t, &mut seen);
            }
        });
        if let Some((t, c, k, l)) = found {
            return Err(Why::NotKept(t, c, k, l));
        }
        let mut out = Vec::new();
        for l in vars {
            if params.iter().any(|(k, _)| *k == l) {
                out.push(l);
            } else {
                return Err(Why::Var(l));
            }
        }
        Ok(out)
    }

    /// The levels of the variables the class's types in a dictionary are
    /// built from, where `t` (under `depth` binders from the top of a
    /// function's body) builds one (#133): kept as descriptors (#170).
    fn dict_type_vars(&self, t: &Tm, depth: usize, out: &mut BTreeSet<usize>) {
        let (h, args) = t.spine();
        let con = match (t, h) {
            (Tm::ConApp(c, _), _) => Some(*c),
            (_, Tm::Con(c)) if args.len() == self.g.arity_con(*c) => Some(*c),
            _ => None,
        };
        if let Some(c) = con {
            let all: Vec<&Tm> = match t {
                Tm::ConApp(_, xs) => xs.iter().collect(),
                _ => args.iter().map(|a| &***a).collect(),
            };
            let np = self.g.arity_ty(self.g.cons[c.0 as usize].ty);
            for k in 0..self.g.cons[c.0 as usize].fields.len() {
                if self.g.is_dict_type_field(c, k) {
                    if let Some(a) = all.get(np + k) {
                        let mut free = BTreeSet::new();
                        crate::core::free_vars(a, 0, &mut free);
                        out.extend(free.into_iter().filter(|i| *i < depth).map(|i| depth - 1 - i));
                    }
                }
            }
        }
        t.each_sub(|x, n| self.dict_type_vars(x, depth + n, out));
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
        if let Some(debug) = self.g.well_known.debug {
            if !self.desc_reqs.contains_key(&debug) {
                if let Some((k, name)) = self.type_formers(debug).into_iter().next() {
                    self.desc_reqs.entry(debug).or_default().insert(k, EqReq { root: debug, param: name });
                }
            }
        }
        // An instance whose class's types are built from its own types: its
        // dictionary keeps their descriptors.
        let defs: Vec<DefId> = self.instances.values().flatten().filter(|i| i.module == self.cur).map(|i| i.def).collect();
        for d in defs {
            let Some(body) = self.g.defs[d.0 as usize].body.clone() else { continue };
            let mut vars = BTreeSet::new();
            self.dict_type_vars(&body, 0, &mut vars);
            let names = self.type_formers(d);
            for l in vars {
                if let Some((_, name)) = names.iter().find(|(k, _)| *k == l) {
                    self.desc_reqs.entry(d).or_default().entry(l).or_insert(EqReq { root: d, param: name.clone() });
                }
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
                    if let Ok(params) = self.check_described(arg, i.lvl, Some(caller)) {
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
        let mut reported = BTreeSet::new();
        for i in insts {
            let reqs: Vec<(usize, EqReq)> = match self.desc_reqs.get(&i.callee) {
                Some(r) => r.iter().map(|(k, v)| (*k, v.clone())).collect(),
                None => continue,
            };
            for (k, why) in reqs {
                let Some(arg) = i.args.get(k) else { continue };
                let Err(why_not) = self.check_described(arg, i.lvl, i.caller) else { continue };
                if !reported.insert((i.span.start, i.span.end, k)) {
                    continue;
                }
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
                let shown = crate::core::show_marked(&self.g, &i.names.to_vec(), &quote(&self.g, i.lvl, arg));
                let label = match why_not {
                    Why::Var(l) => {
                        let var = i.names.get(l).map(|n| n.to_string()).unwrap_or_else(|| "_".into());
                        format!("`{param}` is `{shown}` here, which depends on `{var}`")
                    }
                    Why::NotKept(t, c, k, l) => {
                        let ti = &self.g.tys[t.0 as usize];
                        let np = ti.params.len();
                        let ci = &self.g.cons[c.0 as usize];
                        let from = if l < np { ti.params[l].0.to_string() } else { ci.fields[l - np].0.to_string() };
                        format!(
                            "`{param}` is `{shown}` here, and the type of `{}`'s field `{}` is computed from `{from}`, which isn't kept when the program runs",
                            ti.name, ci.fields[k].0
                        )
                    }
                };
                self.err(
                    Diagnostic::error(
                        "E0293",
                        format!("`{callee}` shows values of type `{param}`{through}, so `{param}` must be known when the program is compiled"),
                        i.span,
                    )
                    .with_label(label),
                );
            }
        }
    }
}
