//! What the checker knows at the cursor, for completion (D142 b): recorded
//! where it meets the cursor's name (`syntax::lexer::CURSOR`), as Lean's
//! elaborator records a `CompletionInfo`.

use super::*;
use crate::syntax::ast::{Expr, ExprKind};
use crate::syntax::lexer::CURSOR;

/// What is known at the cursor.
#[derive(Clone, Debug, Default)]
pub struct CompInfo {
    /// The locals in scope, innermost first.
    pub locals: Vec<CompLocal>,
    /// The type expected there, as shown.
    pub expected: Option<String>,
    /// After `x.`: what `x` is.
    pub member: Option<Member>,
    /// In a `match` arm's pattern: the type matched.
    pub scrutinee: Option<TyId>,
}

#[derive(Clone, Debug)]
pub struct CompLocal {
    pub name: String,
    pub ty: String,
    pub param: bool,
    /// A type, or a type constructor (a type parameter).
    pub is_type: bool,
    pub span: Option<Span>,
}

#[derive(Clone, Debug)]
pub enum Member {
    /// A record: its constructor.
    Record(ConId),
    /// A module, by name.
    Module(String),
    /// A class.
    Class(TyId),
    /// Something with no members.
    None,
}

impl Elab {
    pub fn is_cursor(name: &str) -> bool {
        name == CURSOR
    }

    /// At the cursor, as a name: the locals in scope and the expected type.
    pub fn note_cursor(&mut self, cx: &Cx, expected: Option<&Val>) {
        if self.completion.as_ref().is_some_and(|c| !c.locals.is_empty() || c.expected.is_some()) {
            return;
        }
        let mut locals: Vec<CompLocal> = Vec::new();
        for l in cx.locals.iter().rev() {
            let name = l.name.to_string();
            if name.is_empty() || name.starts_with('$') || name == "_" || locals.iter().any(|x| x.name == name) {
                continue;
            }
            let ty = self.show_val(cx, &l.ty);
            // An auto-bound type parameter's kind may not be known yet.
            let unknown = matches!(self.force(&l.ty), Val::Neutral(crate::core::Head::Meta(_), _));
            let is_type = self.is_type_like(&l.ty) || (unknown && l.mult == Mult::Zero);
            locals.push(CompLocal { name, ty, param: l.param.is_some(), is_type, span: l.span });
        }
        let expected = expected.map(|e| self.show_written(cx, e)).filter(|s| !s.contains('_') && !s.contains('?'));
        let info = self.completion.get_or_insert_with(CompInfo::default);
        info.locals = locals;
        if info.expected.is_none() {
            info.expected = expected;
        }
    }

    /// A type (`Type`) or a type constructor (`Type -> Type`).
    fn is_type_like(&self, ty: &Val) -> bool {
        let mut t = self.force(ty);
        loop {
            match t {
                Val::Univ(_) => return true,
                Val::Pi(_, _, _, _, c) => t = self.force(&apply_closure(&self.g, &c, Val::Error)),
                _ => return false,
            }
        }
    }

    /// At the cursor after `x.`: what `x` is.
    pub fn note_member(&mut self, cx: &mut Cx, x: &Expr) -> (Tm, Val) {
        let member = match &x.kind {
            ExprKind::Con(c) => match self.resolve(c, true) {
                Some(Sym::Ty(t)) if self.class_defs.contains_key(&t) => Some(Member::Class(t)),
                _ => None,
            },
            ExprKind::Var(q) if cx.lookup(q).is_none() => self.qualifier(q).map(Member::Module),
            _ => None,
        };
        let member = match member {
            Some(m) => m,
            None => {
                let (_, ty) = self.infer(cx, x);
                match self.force(&ty) {
                    Val::TyCon(tid, _) if self.g.tys[tid.0 as usize].is_record => Member::Record(self.g.tys[tid.0 as usize].ctors[0]),
                    _ => Member::None,
                }
            }
        };
        self.note_cursor(cx, None);
        if let Some(c) = self.completion.as_mut() {
            c.member = Some(member);
        }
        (Tm::Error, Val::Error)
    }

    /// At the cursor as a `match` arm's pattern: the type matched.
    pub fn note_scrutinee(&mut self, cx: &Cx, ty: &Val) {
        let t = match self.force(ty) {
            Val::TyCon(tid, _) => Some(tid),
            _ => None,
        };
        self.note_cursor(cx, None);
        if let Some(c) = self.completion.as_mut() {
            c.scrutinee = t;
        }
    }
}

/// One completion candidate (§15.5).
#[derive(Clone, Debug)]
pub struct Candidate {
    pub label: String,
    /// keyword, function, lemma, constant, type, class, constructor, field,
    /// parameter, variable, module.
    pub class: &'static str,
    /// Its type or signature.
    pub detail: Option<String>,
    pub doc: Option<String>,
    /// Locals, keywords, the module's own names, then names from elsewhere.
    pub group: u8,
    /// Its type is the expected type.
    pub fits: bool,
}

/// The keywords that can stand at a place (D142 c), from the grammar (§9.2).
pub fn keywords(p: &Place) -> Vec<&'static str> {
    const DECLS: [&str; 10] = ["fn", "partial", "enum", "record", "type", "lemma", "let", "class", "instance", "check"];
    let mut k: Vec<&'static str> = Vec::new();
    match &p.kind {
        PlaceKind::Top { first } => {
            k.push("export");
            k.extend(DECLS);
            if *first {
                k.push("import");
            }
        }
        PlaceKind::Export => k.extend(["abstract", "transparent", "partial", "fn", "enum", "record", "type", "lemma", "let", "class"]),
        PlaceKind::Stmt { first } => {
            k.extend(["let", "have", "if", "match"]);
            if p.proof {
                k.extend(["auto", "admit"]);
            } else {
                k.extend(["when", "try", "par"]);
            }
            if *first {
                k.push("decreasing");
            }
        }
        PlaceKind::Expr => {
            k.extend(["if", "match"]);
            if p.proof {
                k.extend(["have", "auto", "admit"]);
            } else {
                k.extend(["try", "par"]);
            }
        }
        PlaceKind::Cond => k.extend(["forall", "if", "match"]),
        PlaceKind::Type { start: true, field: true } => k.push("ghost"),
        PlaceKind::Type { start: true, field: false } => k.extend(["ghost", "own", "comptime"]),
        PlaceKind::LemmaBody => k.extend(["let", "ensures"]),
        PlaceKind::Proof => k.push("proof"),
        PlaceKind::Else => k.push("else"),
        PlaceKind::Members => k.extend(["fn", "lemma"]),
        PlaceKind::Type { .. } | PlaceKind::Have | PlaceKind::Member | PlaceKind::Pattern | PlaceKind::Import(_) => {}
    }
    k
}

use crate::syntax::parser::{Place, PlaceKind};

impl Elab {
    /// The candidates at `place` in module `module` (D142 a): keywords, then
    /// names, in the order they are offered.
    pub fn candidates(&self, place: &Place, module: &str) -> Vec<Candidate> {
        let info = self.completion.clone().unwrap_or_default();
        let mut out: Vec<Candidate> = Vec::new();
        for k in keywords(place) {
            out.push(Candidate { label: k.to_string(), class: "keyword", detail: None, doc: None, group: 1, fits: false });
        }
        let lemmas = place.proof || place.kind == PlaceKind::Have;
        match &place.kind {
            PlaceKind::Stmt { .. } | PlaceKind::Expr | PlaceKind::Have | PlaceKind::Cond => {
                let cond = place.kind == PlaceKind::Cond;
                for l in &info.locals {
                    if l.is_type && !cond {
                        continue;
                    }
                    out.push(self.local(l, &info));
                }
                self.globals(module, false, lemmas, place.kind == PlaceKind::Have, &info, &mut out);
                if cond || place.kind == PlaceKind::Have {
                    // Classes: a signature's `Ord a`, `have Functor.fmap_id …`.
                    self.classes(module, &mut out);
                }
                self.modules_in_scope(module, &mut out);
            }
            PlaceKind::Type { .. } => {
                // Every type is of type `Type`: none fits better.
                let info = CompInfo { expected: None, ..info.clone() };
                for l in info.locals.iter().filter(|l| l.is_type) {
                    out.push(self.local(l, &info));
                }
                self.globals(module, true, false, false, &info, &mut out);
                out.push(Candidate { label: "Type".into(), class: "type", detail: Some("Type".into()), doc: None, group: 3, fits: false });
                self.modules_in_scope(module, &mut out);
            }
            PlaceKind::Member => match &info.member {
                Some(Member::Record(c)) => {
                    let ci = &self.g.cons[c.0 as usize];
                    for (k, f) in ci.fields.iter().enumerate() {
                        if f.2 != Icit::Expl {
                            continue;
                        }
                        let u = index::Use::Global(index::Target::Field(*c, k));
                        out.push(Candidate { label: f.0.to_string(), class: "field", detail: Some(self.hover_of(&u)), doc: self.doc_of(&u), group: 2, fits: false });
                    }
                }
                Some(Member::Module(m)) => {
                    if let Some(mi) = self.modules.get(m) {
                        let mut names: Vec<(&String, Sym)> = Vec::new();
                        for n in &mi.exported_values {
                            names.push((n, mi.values[n]));
                        }
                        for n in &mi.exported_types {
                            if !mi.exported_values.contains(n) {
                                names.push((n, mi.types[n]));
                            }
                        }
                        for (n, s) in names {
                            if let Some(c) = self.global(n, s, 2, true, &info) {
                                out.push(c);
                            }
                        }
                    }
                }
                Some(Member::Class(t)) => {
                    if let Some(cd) = self.class_defs.get(t) {
                        for m in &cd.members {
                            let n = match m {
                                ast::ClassMember::Fn { name, .. } | ast::ClassMember::Lemma { name, .. } => &name.name,
                            };
                            if let Some(s) = self.modules.get(&cd.module).and_then(|mi| mi.values.get(n)) {
                                if let Some(c) = self.global(n, *s, 2, true, &info) {
                                    out.push(c);
                                }
                            }
                        }
                    }
                }
                Some(Member::None) | None => {}
            },
            PlaceKind::Pattern => {
                let ctors: Vec<ConId> = match info.scrutinee {
                    Some(t) if !self.g.tys[t.0 as usize].is_record => self.g.tys[t.0 as usize].ctors.clone(),
                    _ => {
                        let mi = &self.modules[module];
                        let mut v: Vec<ConId> = mi
                            .values
                            .values()
                            .chain(mi.import_values.values())
                            .filter_map(|s| match s {
                                Sym::Con(c) => Some(*c),
                                _ => None,
                            })
                            .collect();
                        v.sort();
                        v.dedup();
                        v
                    }
                };
                let own = &self.modules[module];
                for c in ctors {
                    let name = self.g.cons[c.0 as usize].name.to_string();
                    let group = if own.values.get(&name) == Some(&Sym::Con(c)) { 2 } else { 3 };
                    let u = index::Use::Global(index::Target::Con(c));
                    out.push(Candidate { label: name, class: "constructor", detail: Some(self.hover_of(&u)), doc: self.doc_of(&u), group, fits: false });
                }
            }
            PlaceKind::Import(prefix) => self.import_paths(prefix, &mut out),
            _ => {}
        }
        // Locals in scope order; the rest by fit, then name.
        let mut seen = HashSet::new();
        out.retain(|c| seen.insert((c.label.clone(), c.group.min(2))));
        out.sort_by(|a, b| {
            a.group.cmp(&b.group).then_with(|| {
                if a.group == 0 {
                    b.fits.cmp(&a.fits)
                } else {
                    b.fits.cmp(&a.fits).then_with(|| a.label.cmp(&b.label))
                }
            })
        });
        out
    }

    fn local(&self, l: &CompLocal, info: &CompInfo) -> Candidate {
        Candidate {
            label: l.name.clone(),
            class: if l.is_type { "type parameter" } else if l.param { "parameter" } else { "variable" },
            detail: Some(format!("{} : {}", l.name, l.ty)),
            doc: None,
            group: 0,
            fits: info.expected.as_deref() == Some(l.ty.as_str()),
        }
    }

    /// The module's own names (group 2) and those its imports bring in (3):
    /// values, or types (`types`).
    fn globals(&self, module: &str, types: bool, lemmas: bool, only_lemmas: bool, info: &CompInfo, out: &mut Vec<Candidate>) {
        let Some(mi) = self.modules.get(module) else { return };
        let (own, imported) = if types { (&mi.types, &mi.import_types) } else { (&mi.values, &mi.import_values) };
        for (group, map) in [(2, own), (3, imported)] {
            for (n, s) in map {
                if types && matches!(s, Sym::Ty(t) if self.class_defs.contains_key(t)) {
                    continue;
                }
                if let Some(c) = self.global(n, *s, group, lemmas, info) {
                    if only_lemmas && c.class != "lemma" {
                        continue;
                    }
                    out.push(c);
                }
            }
        }
    }

    fn classes(&self, module: &str, out: &mut Vec<Candidate>) {
        let Some(mi) = self.modules.get(module) else { return };
        for (group, map) in [(2, &mi.types), (3, &mi.import_types)] {
            for (n, s) in map {
                if let Sym::Ty(t) = s {
                    if self.class_defs.contains_key(t) {
                        let u = index::Use::Global(index::Target::Ty(*t));
                        out.push(Candidate { label: n.clone(), class: "class", detail: Some(self.hover_of(&u)), doc: self.doc_of(&u), group, fits: false });
                    }
                }
            }
        }
    }

    fn modules_in_scope(&self, module: &str, out: &mut Vec<Candidate>) {
        let Some(mi) = self.modules.get(module) else { return };
        for (q, m) in &mi.qualifiers {
            out.push(Candidate { label: q.clone(), class: "module", detail: Some(format!("module {m}")), doc: None, group: 3, fits: false });
        }
    }

    /// A name in scope as a candidate; None for generated names and, unless
    /// `lemmas`, lemmas.
    fn global(&self, name: &str, s: Sym, group: u8, lemmas: bool, info: &CompInfo) -> Option<Candidate> {
        if name.starts_with('$') || name.starts_with("__") || name.contains(' ') {
            return None;
        }
        let t = match s {
            Sym::Def(d) => index::Target::Def(d),
            Sym::Ty(t) => index::Target::Ty(t),
            Sym::Con(c) => index::Target::Con(c),
            Sym::Univ => index::Target::Univ,
            Sym::Len | Sym::Format => {
                return Some(Candidate { label: name.to_string(), class: "function", detail: None, doc: None, group, fits: false });
            }
        };
        let u = index::Use::Global(t);
        let class = match t {
            index::Target::Ty(t) if self.class_defs.contains_key(&t) => "class",
            _ => self.class_of(&u),
        };
        if class == "lemma" && !lemmas {
            return None;
        }
        let fits = match (&info.expected, t) {
            (Some(e), index::Target::Def(d)) => self.result_shown(&self.g.defs[d.0 as usize].ty).as_deref() == Some(e.as_str()),
            (Some(e), index::Target::Con(c)) => self.result_shown(&self.con_type(c)).as_deref() == Some(e.as_str()),
            _ => false,
        };
        Some(Candidate { label: name.to_string(), class, detail: Some(self.hover_of(&u)), doc: self.doc_of(&u), group, fits })
    }

    /// The type a definition gives when applied to all its parameters.
    fn result_shown(&self, ty: &Tm) -> Option<String> {
        let mut names: Vec<Name> = Vec::new();
        let mut t = ty;
        while let Tm::Pi(x, _, _, _, b) = t {
            names.push(x.clone());
            t = b;
        }
        let s = crate::core::show(&self.g, &names, t);
        (!s.contains('#')).then_some(s)
    }

    /// The description of what a name refers to (D128).
    fn doc_of(&self, u: &index::Use) -> Option<String> {
        let (m, span) = self.def_of(u)?;
        let f = self.sources.get(&m)?;
        crate::doc_comment(&f.text, span.start as usize)
    }

    /// Module paths after `import` and the parts before the cursor.
    fn import_paths(&self, prefix: &[String], out: &mut Vec<Candidate>) {
        let mut names: Vec<String> = Vec::new();
        if prefix.first().map(|s| s.as_str()) == Some("std") || prefix.is_empty() {
            for m in stdlib::modules() {
                let parts: Vec<&str> = m.split('.').collect();
                if parts.len() > prefix.len() && parts[..prefix.len()].iter().zip(prefix).all(|(a, b)| a == b) {
                    names.push(parts[prefix.len()].to_string());
                }
            }
        }
        if let Some(dir) = &self.base_dir {
            let d = prefix.iter().fold(dir.clone(), |d, p| d.join(p));
            if let Ok(rd) = std::fs::read_dir(&d) {
                for ent in rd.flatten() {
                    let p = ent.path();
                    let stem = p.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
                    if stem.starts_with('.') || stem.is_empty() {
                        continue;
                    }
                    if p.is_dir() || p.extension().is_some_and(|e| e == "ck") {
                        names.push(stem);
                    }
                }
            }
        }
        names.sort();
        names.dedup();
        for n in names {
            out.push(Candidate { label: n, class: "module", detail: None, doc: None, group: 3, fits: false });
        }
    }
}
