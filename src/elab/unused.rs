//! Unused code (D144): declarations no root reaches (W020), constructors
//! nothing reached builds (W023), record fields nothing reached reads (W024).
//!
//! Every resolved name is a reference from the declaration it is written
//! in (found by its span) to what it names. Marking from the roots (`main`,
//! or a library's exports; every `check`, lemma and instance) over those
//! references finds what is used, mutual recursion that nothing else
//! reaches included.

use super::classes::Origin;
use super::index::Target;
use super::*;
use crate::syntax::ast::{DeclKind, Export};

/// How a name is used.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RefKind {
    /// Named: a function called or passed, a type in a signature.
    Use,
    /// A constructor applied: a value built.
    Build,
    /// A constructor in a pattern: matched, not built.
    Match,
    /// A field read: `r.f`, or bound by a pattern.
    Read,
}

/// One reference, at `span` in `module`.
#[derive(Clone, Debug)]
pub struct Ref {
    pub module: String,
    pub span: Span,
    pub target: Target,
    pub kind: RefKind,
}

/// A declaration of a program module, after classes are desugared.
#[derive(Clone, Debug)]
pub struct Entry {
    pub span: Span,
    /// Its name and where it is written.
    pub name: Option<(String, Span)>,
    /// `function`, `lemma`, `constant`, `enum`, `record`, `type`, `class` or `check`.
    pub what: &'static str,
    pub sym: Option<Sym>,
    pub export: bool,
    pub origin: Origin,
}

/// What references come from.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Owner {
    Root,
    Node(Target),
}

/// The outcome: warnings by module, and the declarations found unused
/// (their branches aren't asked about, D144 d).
pub struct Unused {
    pub warnings: Vec<(String, Diagnostic)>,
    pub dead: Vec<(String, Span)>,
}

impl Elab {
    /// Record a reference from the code being elaborated (not the standard library's).
    pub fn reference(&mut self, span: Span, t: Target, kind: RefKind) {
        if self.stdlib_mode || self.completing.is_some() {
            return;
        }
        self.refs.push(Ref { module: self.cur.clone(), span, target: t, kind });
    }

    /// A value of type `ty` formatted or compared: each of its fields read.
    pub fn observe(&mut self, span: Span, ty: Val) {
        if !self.stdlib_mode && self.completing.is_none() {
            self.observed.push((self.cur.clone(), span, ty));
        }
    }

    /// The fields an observed value of type `ty` has, its parts' included.
    fn observed_fields(&self, ty: &Val, seen: &mut HashSet<TyId>, read: &mut HashSet<(ConId, Rc<str>)>) {
        // High enough for any local the type mentions.
        let t = quote(&self.g, 1024, &crate::core::force_meta(&self.g, ty.clone()));
        self.observed_tm(&t, seen, read);
    }

    fn observed_tm(&self, t: &Tm, seen: &mut HashSet<TyId>, read: &mut HashSet<(ConId, Rc<str>)>) {
        let mut ids = Vec::new();
        ty_cons(t, &mut ids);
        for id in ids {
            if !seen.insert(id) {
                continue;
            }
            for c in &self.g.tys[id.0 as usize].ctors {
                for f in &self.g.cons[c.0 as usize].fields {
                    read.insert((*c, f.0.clone()));
                    self.observed_tm(&f.3, seen, read);
                }
            }
        }
    }

    /// Record module `name`'s declarations.
    pub fn note_decls(&mut self, name: &str, m: &ast::Module, ids: &[Option<Sym>]) {
        if self.stdlib_mode {
            return;
        }
        let mut v = Vec::new();
        for (k, (d, id)) in m.decls.iter().zip(ids).enumerate() {
            let origin = self.decl_origin.get(k).cloned().unwrap_or_default();
            let what = match (&d.kind, &origin) {
                (_, Origin::ClassRecord) => "class",
                (DeclKind::Fn { .. }, _) => "function",
                (DeclKind::Lemma { .. }, _) => "lemma",
                (DeclKind::Const { .. }, _) => "constant",
                (DeclKind::Enum { .. }, _) => "enum",
                (DeclKind::Record { .. }, _) => "record",
                (DeclKind::Alias { .. }, _) => "type",
                _ => "check",
            };
            let name = super::decls::decl_name(d).map(|n| (n.name.clone(), n.span));
            v.push(Entry { span: d.span, name, what, sym: *id, export: d.export != Export::No, origin });
        }
        self.decl_table.insert(name.to_string(), v);
    }

    /// Unused declarations, constructors and fields of the modules `own`
    /// (the program's own, D144); `root` is the module checked.
    pub fn unused(&self, root: &str, own: &[String]) -> Unused {
        let program = self.modules.get(root).is_some_and(|m| m.values.contains_key("main"));
        // Neither `main` nor any export: nothing says what the module is
        // for, so each declaration is a root (D144 h).
        let scratch = !program && self.decl_table.get(root).is_none_or(|v| v.iter().all(|e| !e.export));
        // Each class function or lemma stands for its class.
        let mut member_of: HashMap<DefId, TyId> = HashMap::new();
        for m in own {
            let entries = self.decl_table.get(m).map(|v| v.as_slice()).unwrap_or(&[]);
            for e in entries {
                if let (Origin::ClassMethod | Origin::ClassLemma, Some(Sym::Def(d))) = (&e.origin, e.sym) {
                    let class = entries
                        .iter()
                        .filter(|c| matches!(c.origin, Origin::ClassRecord) && c.span.start <= e.span.start && e.span.end <= c.span.end)
                        .find_map(|c| match c.sym {
                            Some(Sym::Ty(t)) => Some(t),
                            _ => None,
                        });
                    if let Some(t) = class {
                        member_of.insert(d, t);
                    }
                }
            }
        }
        let node_of = |e: &Entry| -> Owner {
            match (&e.origin, e.sym) {
                (Origin::InstDict(_) | Origin::InstMember(_), _) => Owner::Root,
                (Origin::ClassMethod | Origin::ClassLemma, Some(Sym::Def(d))) => match member_of.get(&d) {
                    Some(t) => Owner::Node(Target::Ty(*t)),
                    None => Owner::Root,
                },
                (_, _) if matches!(e.what, "lemma" | "check") => Owner::Root,
                (_, Some(Sym::Def(d))) => Owner::Node(Target::Def(d)),
                (_, Some(Sym::Ty(t))) => Owner::Node(Target::Ty(t)),
                _ => Owner::Root,
            }
        };
        // The declaration a reference is written in: the innermost one
        // containing it (a class's functions are inside the class).
        let owner_at = |m: &str, sp: Span| -> Owner {
            if sp.start >= SYNTHETIC {
                return Owner::Root;
            }
            let Some(entries) = self.decl_table.get(m) else { return Owner::Root };
            entries
                .iter()
                .filter(|e| e.span.start <= sp.start && sp.end <= e.span.end)
                .min_by_key(|e| e.span.end - e.span.start)
                .map_or(Owner::Root, node_of)
        };
        // What a use of `t` also uses.
        let implied = |t: Target| -> Option<Target> {
            match t {
                Target::Con(c) | Target::Field(c, _) => Some(Target::Ty(self.g.cons[c.0 as usize].ty)),
                Target::Def(d) => member_of.get(&d).map(|t| Target::Ty(*t)),
                _ => None,
            }
        };
        let mut edges: HashMap<Owner, Vec<(Target, RefKind)>> = HashMap::new();
        for r in &self.refs {
            if own.contains(&r.module) {
                edges.entry(owner_at(&r.module, r.span)).or_default().push((r.target, r.kind));
            }
        }
        // Roots: `main`, or a library's exports; and everything `check`s,
        // lemmas and instances name.
        let mut live: HashSet<Target> = HashSet::new();
        let mut built: HashSet<ConId> = HashSet::new();
        let mut read: HashSet<(ConId, Rc<str>)> = HashSet::new();
        let mut work: Vec<Owner> = vec![Owner::Root];
        let mark = |t: Target, live: &mut HashSet<Target>, work: &mut Vec<Owner>| {
            let mut t = Some(t);
            while let Some(x) = t {
                if !live.insert(x) {
                    break;
                }
                work.push(Owner::Node(x));
                t = implied(x);
            }
        };
        for m in own {
            for e in self.decl_table.get(m).map(|v| v.as_slice()).unwrap_or(&[]) {
                let is_main = m == root && e.name.as_ref().is_some_and(|n| n.0 == "main") && e.what == "function";
                if !(is_main || (!program && e.export) || (scratch && m == root)) {
                    continue;
                }
                if let Owner::Node(t) = node_of(e) {
                    mark(t, &mut live, &mut work);
                    // An exported type's constructors and fields are its
                    // interface (all of a module's, D144 h).
                    if let Target::Ty(tid) = t {
                        for c in &self.g.tys[tid.0 as usize].ctors {
                            built.insert(*c);
                            for f in &self.g.cons[c.0 as usize].fields {
                                read.insert((*c, f.0.clone()));
                            }
                        }
                    }
                }
            }
        }
        let mut done: HashSet<Owner> = HashSet::new();
        while let Some(o) = work.pop() {
            if !done.insert(o) {
                continue;
            }
            for (t, kind) in edges.get(&o).map(|v| v.as_slice()).unwrap_or(&[]) {
                match (kind, t) {
                    (RefKind::Build, Target::Con(c)) => {
                        built.insert(*c);
                    }
                    (RefKind::Read, Target::Field(c, k)) => {
                        if let Some(f) = self.g.cons[c.0 as usize].fields.get(*k) {
                            read.insert((*c, f.0.clone()));
                        }
                    }
                    _ => {}
                }
                mark(*t, &mut live, &mut work);
            }
        }
        // Formatting or comparing a value reads its fields.
        let mut seen = HashSet::new();
        for (m, sp, ty) in &self.observed {
            if own.contains(m) && match owner_at(m, *sp) {
                Owner::Root => true,
                Owner::Node(t) => live.contains(&t),
            } {
                self.observed_fields(ty, &mut seen, &mut read);
            }
        }
        let mut out = Unused { warnings: Vec::new(), dead: Vec::new() };
        let name_of = |t: Target| -> String {
            match t {
                Target::Def(d) => self.g.defs[d.0 as usize].name.to_string(),
                Target::Ty(t) => self.g.tys[t.0 as usize].name.to_string(),
                _ => String::new(),
            }
        };
        for m in own {
            let text = self.sources.get(m).map(|f| f.text.as_str()).unwrap_or("");
            for e in self.decl_table.get(m).map(|v| v.as_slice()).unwrap_or(&[]) {
                if !matches!(e.origin, Origin::Written | Origin::ClassRecord) || matches!(e.what, "lemma" | "check") {
                    continue;
                }
                let (Some((name, at)), Owner::Node(t)) = (&e.name, node_of(e)) else { continue };
                if !live.contains(&t) {
                    out.dead.push((m.clone(), e.span));
                    // The unused declarations that use this one.
                    let mut users: Vec<String> = Vec::new();
                    for (o, ts) in &edges {
                        let Owner::Node(u) = o else { continue };
                        if *u != t && ts.iter().any(|(x, _)| *x == t || implied(*x) == Some(t)) {
                            let n = name_of(*u);
                            if !n.is_empty() && !users.contains(&n) {
                                users.push(n);
                            }
                        }
                    }
                    users.sort();
                    let mut d = Diagnostic::warning("W020", format!("{} `{name}` is never used", e.what), *at)
                        .with_label(if program { "nothing `main` reaches uses it" } else { "nothing exported reaches it" });
                    if !users.is_empty() {
                        let list = users.iter().map(|u| format!("`{u}`")).collect::<Vec<_>>().join(", ");
                        let them = if users.len() == 1 { "it is unused too" } else { "they are unused too" };
                        d = d.with_note(format!("only {list} use{} it, and {them}", if users.len() == 1 { "s" } else { "" }));
                    }
                    d = d.with_help(if program { "remove it" } else { "remove it, or export it if other modules should use it" });
                    out.warnings.push((m.clone(), d));
                    continue;
                }
                // A used type: its constructors built, its fields read.
                let Target::Ty(tid) = t else { continue };
                if e.what == "class" {
                    continue;
                }
                let info = &self.g.tys[tid.0 as usize];
                let mut never_built = false;
                for c in &info.ctors {
                    if built.contains(c) {
                        continue;
                    }
                    never_built = true;
                    let at = self.decl_at.get(&Target::Con(*c)).map_or(*at, |x| x.1);
                    let cname = &self.g.cons[c.0 as usize].name;
                    let d = if info.is_record {
                        Diagnostic::warning("W023", format!("record `{cname}` is never built"), at)
                            .with_label("nothing used makes one")
                            .with_help("remove it, or build one where it is needed")
                    } else {
                        Diagnostic::warning("W023", format!("constructor `{cname}` is never built"), at)
                            .with_label("nothing used makes this value")
                            .with_help("remove it, with any `match` arm for it")
                    };
                    out.warnings.push((m.clone(), d));
                }
                if !info.is_record || never_built {
                    continue;
                }
                let c = info.ctors[0];
                let mut fields: Vec<(Span, String)> = self
                    .decl_at
                    .iter()
                    .filter_map(|(k, (dm, sp))| match k {
                        Target::Field(fc, _) if *fc == c && dm == m => Some((*sp, text.get(sp.start as usize..sp.end as usize).unwrap_or("").to_string())),
                        _ => None,
                    })
                    .collect();
                fields.sort_by_key(|f| f.0.start);
                for (sp, fname) in fields {
                    if !read.contains(&(c, Rc::from(fname.as_str()))) {
                        out.warnings.push((
                            m.clone(),
                            Diagnostic::warning("W024", format!("field `{fname}` of `{}` is never read", info.name), sp)
                                .with_label("nothing used reads it")
                                .with_help("remove it"),
                        ));
                    }
                }
            }
        }
        out
    }
}

/// The type constructors `t` mentions.
fn ty_cons(t: &Tm, out: &mut Vec<TyId>) {
    match t {
        Tm::TyCon(id) => out.push(*id),
        Tm::TyConApp(id, v) => {
            out.push(*id);
            v.iter().for_each(|x| ty_cons(x, out));
        }
        Tm::App(a, b, ..) | Tm::Pi(_, _, _, a, b) => {
            ty_cons(a, out);
            ty_cons(b, out);
        }
        Tm::TupleTy(v) => v.iter().for_each(|x| ty_cons(x, out)),
        _ => {}
    }
}
