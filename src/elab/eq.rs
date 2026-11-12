//! `==` never compares functions (D125).
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
use std::collections::BTreeSet;

/// Why a type can't be compared.
enum Bad {
    /// It is a function type, or contains this one.
    Fn(Val),
    /// It is a type variable that is not a parameter of the function.
    Var(usize),
}

impl Elab {
    /// The positions of `d`'s leading binders that are type parameters.
    fn type_params(&self, d: DefId) -> Vec<(usize, Name)> {
        let mut out = Vec::new();
        let mut v = eval(&self.g, &Rc::new(Vec::new()), &self.g.defs[d.0 as usize].ty);
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

    /// The type variables `ty` mentions where a value is compared, or why
    /// it can't be compared.
    fn comparable(&self, ty: &Val, depth: usize, seen: &mut Vec<(TyId, Vec<Tm>)>, lvl: usize, vars: &mut BTreeSet<usize>) -> Result<(), Val> {
        if depth > 32 {
            return Ok(());
        }
        match self.force(ty) {
            f @ Val::Pi(..) => Err(f),
            Val::TupleTy(ts) => ts.iter().try_for_each(|t| self.comparable(t, depth + 1, seen, lvl, vars)),
            Val::TyCon(id, args) => {
                let key: Vec<Tm> = args.iter().map(|a| quote(&self.g, lvl, a)).collect();
                if seen.iter().any(|(i, k)| *i == id && k.len() == key.len() && k.iter().zip(&key).all(|(a, b)| tm_eq(a, b))) {
                    return Ok(());
                }
                seen.push((id, key));
                for c in self.g.tys[id.0 as usize].ctors.clone() {
                    let fields = self.g.cons[c.0 as usize].fields.clone();
                    for (i, f) in fields.iter().enumerate() {
                        let mut env = args.clone();
                        env.extend(std::iter::repeat_n(Val::Error, i));
                        let fty = eval(&self.g, &Rc::new(env), &f.3);
                        self.comparable(&fty, depth + 1, seen, lvl, vars)?;
                    }
                }
                Ok(())
            }
            Val::Neutral(Head::Var(l), sp) if sp.is_empty() => {
                vars.insert(l);
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Check `ty` (at level `lvl`, in a body of `owner`): the type
    /// parameters of `owner` it needs comparable, or why it can't be.
    fn check_comparable(&self, ty: &Val, lvl: usize, owner: Option<DefId>) -> Result<Vec<(usize, Name)>, Bad> {
        let mut vars = BTreeSet::new();
        self.comparable(ty, 0, &mut Vec::new(), lvl, &mut vars).map_err(Bad::Fn)?;
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

    /// Why `ty` can't be compared, for a message: "`T` is a function type"
    /// or "`T` contains a function, `A -> B`".
    fn why_not(&self, names: &[Name], lvl: usize, ty: &Val, f: &Val) -> String {
        let shown = show(&self.g, names, &quote(&self.g, lvl, ty));
        if matches!(self.force(ty), Val::Pi(..)) {
            format!("`{shown}` is a function type")
        } else {
            let inner = show(&self.g, names, &quote(&self.g, lvl, f));
            format!("`{shown}` contains a function, `{inner}`")
        }
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
            Err(Bad::Fn(f)) => {
                let shown = show(&self.g, &d.names, &quote(&self.g, d.lvl, &d.ty));
                let why = self.why_not(&d.names, d.lvl, &d.ty, &f);
                self.err(
                    Diagnostic::error("E0263", format!("{} can't compare functions: {why}", d.what), d.span)
                        .with_label(format!("has type `{shown}`"))
                        .with_help("compare what the functions return instead, such as `f x == g x`"),
                );
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
                    Err(Bad::Fn(_)) if matches!(self.force(arg), Val::Pi(..)) => "it is a function type".to_string(),
                    Err(Bad::Fn(f)) => format!("it contains a function, `{}`", show(&self.g, &i.names, &quote(&self.g, i.lvl, &f))),
                    Err(Bad::Var(_)) => "it could be a function type".to_string(),
                };
                let callee = self.g.defs[i.callee.0 as usize].name.to_string();
                let param = self.type_params(i.callee).into_iter().find(|(p, _)| *p == k).map(|(_, n)| n.to_string()).unwrap_or_default();
                let root = self.g.defs[why.root.0 as usize].name.to_string();
                let through = if why.root == i.callee {
                    String::new()
                } else if why.param.as_ref() == param.as_str() {
                    format!(" (through `{root}`)")
                } else {
                    format!(" (through `{root}`, as `{}`)", why.param)
                };
                let shown = show(&self.g, &i.names, &quote(&self.g, i.lvl, arg));
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
