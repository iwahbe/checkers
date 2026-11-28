//! `==` never compares functions, nor capabilities, cowns, futures, files
//! or process handles (#614).
//!
//! (a) `==`/`!=` in compiled code (function bodies, `check`s) on a type that
//! is or contains a function type is E0263. A type parameter of the
//! function being checked is allowed, and recorded: the function now
//! requires that parameter not to be a function type.
//!
//! (b) Each use of a generic function in compiled code records its type
//! arguments (`Inst`). After a module's bodies, the requirements are closed
//! over those uses (a caller passing its own parameter on inherits the
//! requirement) and every argument is checked: E0264.

use super::*;

/// Why a type can't be compared.
enum Bad {
    /// It is, or contains, this function type or built-in type without
    /// equality.
    NoEq(Val),
    /// It is a type variable that is not a parameter of the function.
    Var(usize),
    /// It holds this type, which holds types without end, computed from
    /// its arguments: whether one is a function can't be known.
    Unsure(Val),
}

/// The walk for `==`: a value is compared part by part, field by field and
/// element by element.
struct Comparable;

impl reach::Holds for Comparable {
    fn look(&self, e: &Elab, t: &Val) -> reach::Look {
        use reach::Look;
        match t {
            Val::Pi(..) => Look::Hit,
            // An array compares element by element (#624).
            Val::TyCon(id, args) if Some(*id) == e.g.well_known.array => match args.first() {
                Some(a) => Look::Parts(vec![a.clone()]),
                None => Look::Leaf,
            },
            Val::TyCon(id, _) if e.no_equality(*id).is_some() => Look::Hit,
            Val::TupleTy(ts) => Look::Parts(ts.to_vec()),
            Val::TyCon(id, args) => Look::Fields(*id, args.to_vec()),
            Val::Neutral(Head::Var(l), sp) if sp.is_empty() => Look::Var(*l),
            _ => Look::Leaf,
        }
    }

    fn field(&self, _: &Elab, _: ConId, _: usize) -> bool {
        true
    }

    fn by_head(&self) -> bool {
        true
    }
}

impl Elab {
    /// The positions of `d`'s leading binders that are type parameters.
    fn type_params(&self, d: DefId) -> Vec<(usize, Name)> {
        let mut out = Vec::new();
        let mut v = eval(&self.g, &crate::core::Env::new(), &self.g.defs[d.0 as usize].ty);
        let mut k = 0;
        while let Val::Pi(x, _, _, dom, c) = self.force(&v) {
            if matches!(self.force(&dom), Val::Univ(_)) {
                out.push((k, x.clone()));
            }
            v = apply_closure(&self.g, &c, Val::var(k));
            k += 1;
        }
        out
    }

    /// What a built-in type without equality is (#614 c): `None` for the
    /// built-in types that compare and for every declared type.
    fn no_equality(&self, id: TyId) -> Option<&'static str> {
        let ti = &self.g.tys[id.0 as usize];
        if !ti.is_abstract || !ti.ctors.is_empty() || !ti.module.starts_with("std.") {
            return None;
        }
        match &*ti.name {
            "Int" | "String" | "Bytes" | "Bag" | "Decimal" | "IoError" => None,
            "Cown" => Some("a cown"),
            "Future" => Some("a future"),
            "File" => Some("a file"),
            "Child" | "Killer" => Some("a process handle"),
            _ => Some("a capability"),
        }
    }

    /// What a type that can't be compared is, or contains: "it is a
    /// function type", "it contains a capability, `Term`".
    fn why_not(&self, names: &[Name], lvl: usize, ty: &Val, bad: &Val) -> String {
        let what = |v: &Val| match self.force(v) {
            Val::TyCon(id, _) => self.no_equality(id).unwrap_or("a function"),
            _ => "a function",
        };
        if matches!(self.force(ty), Val::Pi(..)) {
            "it is a function type".to_string()
        } else if tm_eq(&quote(&self.g, lvl, ty), &quote(&self.g, lvl, bad)) {
            format!("it is {}", what(bad))
        } else {
            format!("it contains {}, `{}`", what(bad), crate::core::show_marked(&self.g, names, &quote(&self.g, lvl, bad)))
        }
    }

    /// Why a type holding `t` (`Bad::Unsure`) can't be compared.
    fn unsure_why(&self, names: &[Name], lvl: usize, t: &Val) -> String {
        let shown = crate::core::show_marked(&self.g, names, &quote(&self.g, lvl, t));
        format!("it holds `{shown}`, whose parts' types are computed from its arguments at every depth, so whether one is a function can't be known")
    }

    /// Check `ty` (at level `lvl`, in a body of `owner`): the type
    /// parameters of `owner` it needs comparable, or why it can't be.
    fn check_comparable(&self, ty: &Val, lvl: usize, owner: Option<DefId>) -> Result<Vec<(usize, Name)>, Bad> {
        let vars = match self.reach(&Comparable, lvl, ty) {
            (reach::Found::Nothing, vars) => vars,
            (reach::Found::Hit(t), _) => return Err(Bad::NoEq(t)),
            (reach::Found::Unsure(t), _) => return Err(Bad::Unsure(t)),
        };
        let params = owner.map(|d| self.type_params(d)).unwrap_or_default();
        let mut out = Vec::new();
        for l in vars {
            match params.iter().find(|(k, _)| *k == l) {
                Some(p) => out.push(p.clone()),
                None => return Err(Bad::Var(l)),
            }
        }
        Ok(out)
    }

    /// (a): a `==` or `!=` in compiled code.
    pub(super) fn solve_comparable(&mut self, d: &Deferred) {
        match self.check_comparable(&d.ty, d.lvl, d.owner) {
            Ok(params) => {
                if let Some(owner) = d.owner {
                    let reqs = self.eq_reqs.entry(owner).or_default();
                    for (k, name) in params {
                        reqs.entry(k).or_insert(EqReq { root: owner, param: name });
                    }
                }
            }
            Err(Bad::NoEq(f)) => {
                let shown = crate::core::show_marked(&self.g, &d.names.to_vec(), &quote(&self.g, d.lvl, &d.ty));
                let why = self.why_not(&d.names.to_vec(), d.lvl, &d.ty, &f);
                let mut diag = Diagnostic::error("E0263", format!("{} can't compare `{shown}`: {why}", d.what), d.span)
                    .with_label(format!("has type `{shown}`"));
                if matches!(self.force(&f), Val::Pi(..)) {
                    diag = diag.with_help("compare what the functions return instead, such as `f x == g x`");
                }
                self.err(diag);
            }
            Err(Bad::Unsure(t)) => {
                let shown = crate::core::show_marked(&self.g, &d.names.to_vec(), &quote(&self.g, d.lvl, &d.ty));
                let why = self.unsure_why(&d.names.to_vec(), d.lvl, &t);
                self.err(Diagnostic::error("E0263", format!("{} can't compare `{shown}`: {why}", d.what), d.span).with_label(format!("has type `{shown}`")));
            }
            Err(Bad::Var(l)) => {
                let shown = d.names.get(l).map(|n| n.to_string()).unwrap_or_else(|| "_".into());
                self.err(
                    Diagnostic::error("E0263", format!("{} can't compare values of type `{shown}`: it could be a function type", d.what), d.span)
                        .with_label(format!("has type `{shown}`")),
                );
            }
        }
    }

    /// (b): close the requirements over this module's uses of generic
    /// functions, then check every use.
    pub(super) fn resolve_insts(&mut self) {
        let insts = std::mem::take(&mut self.insts);
        let mut uses = insts.clone();
        uses.extend(std::mem::take(&mut self.dict_insts));
        self.resolve_descs(&uses);
        loop {
            let mut changed = false;
            for i in &insts {
                let Some(caller) = i.caller else { continue };
                let reqs: Vec<(usize, EqReq)> = match self.eq_reqs.get(&i.callee) {
                    Some(r) => r.iter().map(|(k, v)| (*k, v.clone())).collect(),
                    None => continue,
                };
                for (k, why) in reqs {
                    let Some(arg) = i.args.get(k) else { continue };
                    if let Ok(params) = self.check_comparable(arg, i.lvl, Some(caller)) {
                        let mine = self.eq_reqs.entry(caller).or_default();
                        for (p, _) in params {
                            if let std::collections::btree_map::Entry::Vacant(e) = mine.entry(p) {
                                e.insert(why.clone());
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
        for i in &insts {
            let reqs: Vec<(usize, EqReq)> = match self.eq_reqs.get(&i.callee) {
                Some(r) => r.iter().map(|(k, v)| (*k, v.clone())).collect(),
                None => continue,
            };
            for (k, why) in reqs {
                let Some(arg) = i.args.get(k) else { continue };
                let bad = match self.check_comparable(arg, i.lvl, i.caller) {
                    Ok(_) => continue,
                    Err(Bad::NoEq(f)) => self.why_not(&i.names.to_vec(), i.lvl, arg, &f),
                    Err(Bad::Var(_)) => "it could be a function type".to_string(),
                    Err(Bad::Unsure(t)) => self.unsure_why(&i.names.to_vec(), i.lvl, &t),
                };
                let callee = self.g.defs[i.callee.0 as usize].name.to_string();
                let param = self.type_params(i.callee).into_iter().find(|(p, _)| *p == k).map(|(_, n)| n.to_string()).unwrap_or_default();
                let root = self.g.defs[why.root.0 as usize].name.to_string();
                let root_home = &self.g.defs[why.root.0 as usize].module;
                let through = if why.root == i.callee {
                    String::new()
                } else if self.hidden_from(&self.cur, crate::core::Marked::Def(why.root)) {
                    // Another package's private function isn't named (§6 rule 9).
                    format!(" (through a private function of `{root_home}`)")
                } else if why.param.as_ref() == param.as_str() {
                    format!(" (through `{root}`)")
                } else {
                    format!(" (through `{root}`, as `{}`)", why.param)
                };
                let shown = crate::core::show_marked(&self.g, &i.names.to_vec(), &quote(&self.g, i.lvl, arg));
                self.err(
                    Diagnostic::error(
                        "E0264",
                        format!("`{callee}` compares values of type `{param}` with `==`{through}, so `{param}` can't be `{shown}`: {bad}"),
                        i.span,
                    )
                    .with_label(format!("`{param}` is `{shown}` here")),
                );
            }
        }
    }
}
