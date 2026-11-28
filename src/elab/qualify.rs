//! Names in messages: two different declarations of the same name in one
//! diagnostic (`T` from two modules) are each shown as the module the
//! diagnostic is in refers to it: unqualified if that name is it there,
//! else through the qualifier of an import of its module (`b.T`), else by
//! its module's full name. Other names are shown as declared, except
//! another package's private declarations, which are never named (§6
//! rule 9).
//!
//! The printer marks each global it names (`core::show_marked`); a
//! diagnostic's text is unmarked once it is complete, when it is filed.

use super::{Elab, ModuleInfo, Sym};
use crate::core::{marks, show_marked, unmark, Icit, Marked, Scope, Tm};
use crate::diag::Diagnostic;
use std::collections::{BTreeMap, BTreeSet};

impl Elab {
    /// The module that declares `m`.
    fn home_of(&self, m: Marked) -> &str {
        match m {
            Marked::Def(d) => &self.g.defs[d.0 as usize].module,
            Marked::Ty(t) => &self.g.tys[t.0 as usize].module,
            Marked::Con(c) => &self.g.tys[self.g.cons[c.0 as usize].ty.0 as usize].module,
            Marked::Var { .. } => "",
        }
    }

    /// `m` is a declaration that a module of another package than
    /// `module`'s keeps private (§6 rule 9): a diagnostic in `module`
    /// never names it.
    pub fn hidden_from(&self, module: &str, m: Marked) -> bool {
        let (name, sym) = match m {
            Marked::Def(d) => (&self.g.defs[d.0 as usize].name, Sym::Def(d)),
            Marked::Ty(t) => (&self.g.tys[t.0 as usize].name, Sym::Ty(t)),
            Marked::Con(c) => (&self.g.cons[c.0 as usize].name, Sym::Con(c)),
            Marked::Var { .. } => return false,
        };
        let home = self.home_of(m);
        if self.package_of(home) == self.package_of(module) {
            return false;
        }
        // An instance's function, or the function building its dictionary.
        if let Sym::Def(d) = sym {
            if self.inst_fns.contains(&d) || self.dict_defs.contains(&d) {
                return false;
            }
        }
        // Declared by its module under its name (not an instance's
        // function, nor one the compiler made), and not exported.
        self.modules.get(home).is_some_and(|mi| {
            let (all, exported) = if matches!(sym, Sym::Ty(_)) { (&mi.types, &mi.exported_types) } else { (&mi.values, &mi.exported_values) };
            all.get(&**name) == Some(&sym) && !exported.contains(&**name)
        })
    }

    /// Record, for native code, the functions a runtime error in a program
    /// whose code is in `module` never names (`Globals::hidden`): those
    /// `hidden_from` it.
    pub fn hide_private(&self, module: &str) {
        let hidden = (0..self.g.defs.len() as u32).map(crate::core::DefId).filter(|d| self.hidden_from(module, Marked::Def(*d))).collect();
        *self.g.hidden.borrow_mut() = hidden;
    }

    /// The module of `full` (`std.prelude.string_le`), a declaration a
    /// module of another package than `module`'s keeps private (§6 rule
    /// 9), if it is one.
    pub fn hidden_home(&self, module: &str, full: &str) -> Option<String> {
        let (home, name) = full.rsplit_once('.')?;
        let sym = self.modules.get(home)?.values.get(name)?;
        let m = match *sym {
            Sym::Def(d) => Marked::Def(d),
            Sym::Con(c) => Marked::Con(c),
            Sym::Ty(t) => Marked::Ty(t),
            _ => return None,
        };
        self.hidden_from(module, m).then(|| home.to_string())
    }

    /// How a diagnostic in `module` speaks of the sealed function `s`, the
    /// first of `collect_sealed`'s, in a term under the locals `names`: by
    /// its name, or, when it is another package's private function (§6
    /// rule 9), by what was called to reach it. With whether that is
    /// plural (`<=`, `<`, `>=` and `>` on `String`), and whether the
    /// function is such a private one.
    pub fn sealed_subject<S: Scope + ?Sized>(&self, module: &str, s: &crate::elab::Sealed, names: &S) -> (String, bool, bool) {
        if !self.hidden_from(module, Marked::Def(s.def)) {
            return (format!("`{}`", show_marked(&self.g, names, &Tm::Def(s.def))), false, false);
        }
        let Some(via) = &s.via else { return ("this".to_string(), false, true) };
        let mut h = via;
        let mut implicit = Vec::new();
        while let Tm::App(f, a, i, _) = h {
            if *i == Icit::Impl {
                implicit.push(a.clone());
            }
            h = f;
        }
        implicit.reverse();
        let Tm::Def(f) = h else { return ("this".to_string(), false, true) };
        let called = &self.g.defs[f.0 as usize];
        // A class's function at an instance: its operators, or its name,
        // at the instance's types.
        let class = self.class_defs.values().find(|c| {
            *c.module == *called.module
                && c.members.iter().any(|m| matches!(m, crate::syntax::ast::ClassMember::Fn { name, .. } if *name.name == *called.name))
        });
        let Some(class) = class.filter(|_| self.g.well_known.class_fns.contains(f)) else {
            return (format!("`{}`", show_marked(&self.g, names, &Tm::Def(*f))), false, true);
        };
        let at: Vec<String> = implicit.iter().take(class.params.len()).map(|t| show_marked(&self.g, names, t)).collect();
        let at = at.join("`, `");
        let ops: Vec<&str> = if *called.module == *"std.prelude" { crate::elab::Elab::spellings(&called.name) } else { Vec::new() };
        match ops.as_slice() {
            [] => (format!("`{}.{}` at `{at}`", class.name, called.name), false, true),
            [one] => (format!("`{one}` on `{at}`"), false, true),
            [init @ .., last] => {
                let init: Vec<String> = init.iter().map(|o| format!("`{o}`")).collect();
                (format!("{} and `{last}` on `{at}`", init.join(", ")), true, true)
            }
        }
    }

    /// How `module` refers to `m`, named `name`: unqualified, or with a
    /// qualifier, and whether that is unqualified.
    fn referred_as(&self, module: &str, m: Marked, name: &str) -> (String, bool) {
        let home = self.home_of(m).to_string();
        let Some(mi) = self.modules.get(module) else { return (format!("{home}.{name}"), false) };
        let sym = match m {
            Marked::Def(d) => Sym::Def(d),
            Marked::Ty(t) => Sym::Ty(t),
            Marked::Con(c) => Sym::Con(c),
            Marked::Var { .. } => return (name.to_string(), true),
        };
        if [true, false].into_iter().any(|type_pos| in_scope(mi, name, type_pos) == Some(sym)) {
            return (name.to_string(), true);
        }
        if home == module {
            return (name.to_string(), true);
        }
        // The shortest qualifier for its module, then the first.
        let q = mi.qualifiers.iter().filter(|(_, to)| **to == home).map(|(q, _)| q).min_by_key(|q| (q.len(), (*q).clone()));
        match q {
            Some(q) => (format!("{q}.{name}"), false),
            None => (format!("{home}.{name}"), false),
        }
    }

    /// How each marked global in `texts` is shown in `module`: the name
    /// as declared, or, for two different declarations of one name, as
    /// the module refers to each. With a `help:` saying where each comes
    /// from when one of them is imported unqualified.
    ///
    /// A local hidden where the diagnostic is, by a later one of its name,
    /// is told apart too: shown with a number (`a1`), and a note says
    /// where each is bound.
    fn names_for(&self, module: &str, texts: &[&str]) -> (BTreeMap<Marked, String>, Option<String>, Vec<String>) {
        let mut by_name: BTreeMap<String, BTreeSet<Marked>> = BTreeMap::new();
        let mut vars: BTreeMap<String, BTreeMap<u32, Marked>> = BTreeMap::new();
        let mut shown = BTreeMap::new();
        for t in texts {
            for (m, n) in marks(t) {
                match m {
                    Marked::Var { level, .. } => {
                        vars.entry(n).or_default().insert(level, m);
                    }
                    // Another package's private declaration: not named.
                    _ if self.hidden_from(module, m) => {
                        shown.insert(m, "…".to_string());
                    }
                    _ => {
                        by_name.entry(n).or_default().insert(m);
                    }
                }
            }
        }
        let mut helps = Vec::new();
        let notes = self.name_locals(module, texts, &vars, &mut shown);
        for (name, ms) in &by_name {
            // A record's constructor shares its type's name: one module's
            // declarations of a name are one name.
            let homes: BTreeSet<&str> = ms.iter().map(|m| self.home_of(*m)).collect();
            if homes.len() < 2 {
                for m in ms {
                    shown.insert(*m, name.clone());
                }
                continue;
            }
            let mut refs: Vec<(Marked, String, bool)> = ms
                .iter()
                .map(|m| {
                    let (r, plain) = self.referred_as(module, *m, name);
                    (*m, r, plain)
                })
                .collect();
            // Two still shown alike (a type and another module's
            // constructor, both unqualified): by their modules' names.
            let alike = |refs: &[(Marked, String, bool)], i: usize| {
                refs.iter().enumerate().any(|(j, r)| j != i && r.1 == refs[i].1 && self.home_of(r.0) != self.home_of(refs[i].0))
            };
            let clash: Vec<usize> = (0..refs.len()).filter(|i| alike(&refs, *i)).collect();
            for i in clash {
                let home = self.home_of(refs[i].0).to_string();
                refs[i].1 = format!("{home}.{name}");
                refs[i].2 = false;
            }
            let imported = refs.iter().find(|r| r.2 && self.home_of(r.0) != module);
            if let Some((m, r, _)) = imported {
                let mut parts = vec![format!("`{r}` here is from module `{}`, imported unqualified", self.home_of(*m))];
                let mut seen = BTreeSet::new();
                for (o, ro, _) in &refs {
                    if ro != r && seen.insert(ro.clone()) {
                        parts.push(format!("`{ro}` is from module `{}`", self.home_of(*o)));
                    }
                }
                helps.push(parts.join("; "));
            }
            for (m, r, _) in refs {
                shown.insert(m, r);
            }
        }
        (shown, (!helps.is_empty()).then(|| helps.join("; ")), notes)
    }

    /// Names for the locals marked in `texts` (`vars`, by name and
    /// level): the one the name means where the diagnostic is by its name;
    /// one hidden there by another of its name numbered (`a1`, a name not
    /// otherwise in the texts), with a note saying where each is bound.
    fn name_locals(
        &self,
        module: &str,
        texts: &[&str],
        vars: &BTreeMap<String, BTreeMap<u32, Marked>>,
        shown: &mut BTreeMap<Marked, String>,
    ) -> Vec<String> {
        let line = |at: Option<u32>| {
            let f = self.sources.get(module)?;
            let sp = self.real_span(module, crate::source::Span { start: at?, end: at? });
            Some(f.line_col(sp.start).0)
        };
        let mut taken: BTreeSet<String> = texts
            .iter()
            .flat_map(|t| {
                crate::core::unmark(t, &mut |_, n| n.to_string())
                    .split(|c: char| !c.is_alphanumeric() && c != '_')
                    .map(str::to_string)
                    .collect::<Vec<_>>()
            })
            .collect();
        let mut notes = Vec::new();
        for (name, levels) in vars {
            // Innermost first: the lowest number for the nearest.
            for m in levels.values().rev() {
                let Marked::Var { at, hidden_by: Some(by), avoid, .. } = *m else {
                    shown.insert(*m, name.clone());
                    continue;
                };
                // Not a name in the texts, nor one in scope there: a local,
                // or one the module declares or imports.
                let declared = |n: &str| self.modules.get(module).is_some_and(|mi| in_scope(mi, n, false).is_some());
                let mut k = 1;
                while taken.contains(&format!("{name}{k}")) || (k <= 64 && avoid & (1 << (k - 1)) != 0) || declared(&format!("{name}{k}")) {
                    k += 1;
                }
                let renamed = format!("{name}{k}");
                taken.insert(renamed.clone());
                shown.insert(*m, renamed.clone());
                notes.push(match (line(at), line(by)) {
                    (Some(a), Some(b)) => format!("`{renamed}` is the `{name}` bound on line {a}, hidden here by the `{name}` bound on line {b}"),
                    (Some(a), None) => format!("`{renamed}` is the `{name}` bound on line {a}, hidden here by another `{name}`"),
                    _ => format!("`{renamed}` is an outer `{name}`, hidden here by another `{name}`"),
                });
            }
        }
        notes
    }

    /// `d`'s text with the globals it names shown as `module` refers to
    /// them (see `names_for`).
    pub fn name_globals(&self, module: &str, d: &mut Diagnostic) {
        let mut texts: Vec<&str> = vec![&d.message];
        texts.extend(d.label.as_deref());
        texts.extend(d.help.as_deref());
        texts.extend(d.notes.iter().map(|n| n.as_str()));
        if !texts.iter().any(|t| t.contains('\u{1}')) {
            return;
        }
        let (shown, help, notes) = self.names_for(module, &texts);
        let mut f = |m: Marked, n: &str| shown.get(&m).cloned().unwrap_or_else(|| n.to_string());
        d.message = unmark(&d.message, &mut f);
        d.label = d.label.as_deref().map(|l| unmark(l, &mut f));
        d.help = d.help.as_deref().map(|h| unmark(h, &mut f));
        for n in &mut d.notes {
            *n = unmark(n, &mut f);
        }
        d.notes.extend(notes);
        if let Some(h) = help {
            match d.help {
                None => d.help = Some(h),
                Some(_) => d.notes.push(h),
            }
        }
    }

    /// Text for a tool (hover, completion) with the globals it names
    /// shown as `module` refers to them (see `names_for`).
    pub fn named_in(&self, module: &str, s: &str) -> String {
        if !s.contains('\u{1}') {
            return s.to_string();
        }
        let (shown, _, _) = self.names_for(module, &[s]);
        unmark(s, &mut |m, n| shown.get(&m).cloned().unwrap_or_else(|| n.to_string()))
    }
}

/// What `name` is in `mi`'s scope, as `Elab::resolve` finds it.
fn in_scope(mi: &ModuleInfo, name: &str, type_pos: bool) -> Option<Sym> {
    let firsts = if type_pos { [&mi.types, &mi.import_types] } else { [&mi.values, &mi.import_values] };
    let seconds = if type_pos { [&mi.values, &mi.import_values] } else { [&mi.types, &mi.import_types] };
    firsts.into_iter().chain(seconds).find_map(|map| map.get(name).copied())
}
