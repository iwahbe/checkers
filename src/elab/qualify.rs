//! Names in messages: two different declarations of the same name in one
//! diagnostic (`T` from two modules) are each shown as the module the
//! diagnostic is in refers to it: unqualified if that name is it there,
//! else through the qualifier of an import of its module (`b.T`), else by
//! its module's full name. Other names are shown as declared.
//!
//! The printer marks each global it names (`core::show_marked`); a
//! diagnostic's text is unmarked once it is complete, when it is filed.

use super::{Elab, ModuleInfo, Sym};
use crate::core::{marks, unmark, Marked};
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
        for t in texts {
            for (m, n) in marks(t) {
                match m {
                    Marked::Var { level, .. } => {
                        vars.entry(n).or_default().insert(level, m);
                    }
                    _ => {
                        by_name.entry(n).or_default().insert(m);
                    }
                }
            }
        }
        let mut shown = BTreeMap::new();
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
                let Marked::Var { at, hidden_by: Some(by), .. } = *m else {
                    shown.insert(*m, name.clone());
                    continue;
                };
                let mut k = 1;
                while taken.contains(&format!("{name}{k}")) {
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
