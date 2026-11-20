//! Modules, imports, and declarations.

use super::*;
use crate::syntax::ast::{Constraint, DeclKind, Export, Expr, ExprKind, Ident};
use std::collections::BTreeSet;

/// A type at its arguments, each reduced to whether it has a value (D183).
type TypeInstance = (TyId, Vec<bool>);

/// A constructor invariant while its fields are elaborated: the predicate,
/// its text and span, the level it was made at, and the field's alias if it
/// comes from a refinement-alias field type.
type FieldInv = (Tm, String, Span, usize, Option<(usize, DefId)>);

/// Signature of a function or lemma, elaborated into a context.
pub struct Sig {
    pub cx: Cx,
    /// (name, mult, icit, type) for every binder, implicit ones first.
    pub binders: Vec<(Name, Mult, Icit, Tm)>,
    pub result: Tm,
    pub n_implicit: usize,
    /// Header predicates, over the binders then the result (§7.1).
    pub preds: Vec<Pred>,
    pub result_name: String,
    /// Binder positions marked `comptime` (D59).
    pub comptime: Vec<usize>,
    /// Named preconditions (D137): name and index in `preds`.
    pub hyps: Vec<(String, usize)>,
    /// Parameters whose refinements mention later parameters (#102): the
    /// binder, and its refined type over all the binders. The binder's own
    /// type in `binders` is the type without its refinements.
    pub late: Vec<Late>,
}

impl Elab {
    pub fn elab_module(&mut self, name: &str, m: &ast::Module, is_stdlib: bool) {
        if self.loading.iter().any(|n| n == name) {
            return;
        }
        self.loading.push(name.to_string());
        self.cur = name.to_string();
        self.stdlib_mode = is_stdlib;
        self.modules.insert(name.to_string(), ModuleInfo { name: name.to_string(), ..Default::default() });

        self.imports(m, name);
        // `CHECKERS_ELAB_TIME=1`: each module's elaboration time, its imports'
        // not included (to find what makes the types phase slow).
        let started = std::time::Instant::now();
        self.cur = name.to_string();
        self.stdlib_mode = is_stdlib;
        // Classes and instances become records, functions and lemmas (D136).
        self.pending_insts.clear();
        let (desugared, origins) = self.desugar_classes(m);
        self.decl_origin = origins;
        let m = &desugared;
        let ids = self.register(m);
        self.register_classes(m, &ids);
        self.decl_spans.insert(name.to_string(), m.decls.iter().zip(&ids).map(|(d, id)| (d.span, *id)).collect());
        self.note_decls(name, m, &ids);
        self.phase_type_params(m, &ids);
        // Declarations in the order of what they use, not of the file (D65).
        let dicts: Vec<usize> =
            self.decl_origin.iter().enumerate().filter(|(_, o)| matches!(o, super::classes::Origin::InstDict(_))).map(|(k, _)| k).collect();
        let plan = super::order::plan(m, &dicts);
        for chain in &plan.cycles {
            let name = |k: usize| decl_name(&m.decls[k]).map(|n| n.name.clone()).unwrap_or_default();
            let span = decl_name(&m.decls[chain[0]]).map(|n| n.span).unwrap_or(m.decls[chain[0]].span);
            let shown: Vec<String> = chain.iter().map(|k| format!("`{}`", name(*k))).collect();
            let msg = if chain.len() <= 2 {
                format!("`{}` depends on itself", name(chain[0]))
            } else {
                format!("`{}` depends on itself: {}", name(chain[0]), shown.join(" → "))
            };
            let aliases = chain.iter().all(|k| matches!(m.decls[*k].kind, ast::DeclKind::Alias { .. }));
            let help = if aliases {
                "an alias stands for its definition, so this would never end; a type can contain itself only through an `enum` or a `record`"
            } else {
                "a type, signature or constant can't need its own value; break the chain (recursion between function bodies is fine)"
            };
            self.err(Diagnostic::error("E0225", msg, span).with_help(help));
        }
        let mut sigs: HashMap<usize, Sig> = HashMap::new();
        for group in &plan.groups {
            let keep: HashSet<usize> = group.iter().map(|n| match n {
                super::order::Node::Head(k) | super::order::Node::Body(k) => *k,
            }).collect();
            let mask: Vec<Option<Sym>> = ids.iter().enumerate().map(|(k, s)| if keep.contains(&k) { *s } else { None }).collect();
            match group[0] {
                super::order::Node::Head(k) => match &m.decls[k].kind {
                    DeclKind::Enum { .. } | DeclKind::Record { .. } | DeclKind::Alias { .. } => {
                        self.phase_aliases(m, &mask);
                        self.phase_ctors(m, &mask);
                    }
                    DeclKind::Const { .. } => self.phase_consts(m, &mask),
                    _ => {
                        sigs.extend(self.phase_signatures(m, &mask));
                        self.phase_lemma_statements(m, &mask, &mut sigs);
                        self.phase_measures(m, &mask, &sigs);
                    }
                },
                super::order::Node::Body(k) => {
                    let one: HashMap<usize, Sig> = sigs.remove(&k).map(|s| (k, s)).into_iter().collect();
                    self.phase_bodies(m, &mask, one, false);
                }
            }
        }
        self.phase_positivity(m, &ids);
        self.phase_bodies(m, &ids, HashMap::new(), true);
        self.check_termination();
        // A transparent function's private helpers are visible to the prover
        // too, or its body would say nothing (D54): close the set over calls.
        let mut stack: Vec<DefId> = self.transparent.iter().copied().filter(|d| *self.g.defs[d.0 as usize].module == *name).collect();
        while let Some(d) = stack.pop() {
            let mut used = Vec::new();
            if let Some(b) = &self.g.defs[d.0 as usize].body {
                defs_in(b, &mut used);
            }
            for u in used {
                let info = &self.g.defs[u.0 as usize];
                if *info.module == *name && info.body.is_some() && !info.opaque && self.transparent.insert(u) {
                    stack.push(u);
                }
            }
        }
        // Seal the module's functions (D54): importers see signatures only.
        for (d, id) in m.decls.iter().zip(&ids) {
            if let (DeclKind::Fn { .. }, Some(Sym::Def(did))) = (&d.kind, id) {
                // A transparent function's private helpers stay unsealed too.
                if d.export != Export::Transparent && !self.transparent.contains(did) {
                    self.g.defs[did.0 as usize].sealed = true;
                }
            }
        }
        self.loading.pop();
        if std::env::var_os("CHECKERS_ELAB_TIME").is_some() {
            eprintln!("{name}: {:.1} ms", started.elapsed().as_secs_f64() * 1000.0);
        }
    }

    // ── imports ─────────────────────────────────────────────────────────────

    fn imports(&mut self, m: &ast::Module, name: &str) {
        if name != "std.prelude" {
            self.load_stdlib("std.prelude");
            let p = &self.modules["std.prelude"];
            let ts: Vec<(String, Sym)> =
                p.exported_types.iter().map(|n| (n.clone(), p.types[n])).collect();
            let vs: Vec<(String, Sym)> =
                p.exported_values.iter().map(|n| (n.clone(), p.values[n])).collect();
            let me = self.modules.get_mut(name).unwrap();
            me.import_types.extend(ts);
            me.import_values.extend(vs);
        }
        for imp in &m.imports {
            let path = imp.path.dotted();
            self.cur = name.to_string();
            // The first component says where a module comes from (D105): `std`,
            // a dependency (D111), or else this package's own files.
            let from_std = path.starts_with("std.");
            let here = self.package_of(name);
            let first = path.split('.').next().unwrap_or("").to_string();
            let pkgs = super::stdlib::packages();
            let dep = (!from_std && path.contains('.') && pkgs.dirs.contains_key(&first)).then(|| first.clone());
            if let Some(d) = &dep {
                let allowed = here != "std" && pkgs.uses.get(&here).is_some_and(|u| u.contains(d));
                if !allowed {
                    let who = if here == "." { "this program".to_string() } else { format!("package `{here}`") };
                    let mut diag = Diagnostic::error("E0227", format!("`{d}` is not a dependency of {who}"), imp.path.span)
                        .with_label(format!("{who} doesn't list `{d}` in its `dependencies`"));
                    diag = if *d == here {
                        let rel = &path[d.len() + 1..];
                        diag.with_help(format!("a package imports its own modules by their path in it: `import {rel}`"))
                    } else {
                        diag.with_help(format!("add `{d}` to `dependencies` in checkers.json"))
                    };
                    self.err(diag);
                    self.import_failed(name, imp);
                    continue;
                }
            }
            // The module's name in this build.
            let key = match (&dep, here.as_str()) {
                (Some(_), _) => path.clone(),
                (None, _) if from_std => path.clone(),
                (None, ".") | (None, "std") => path.clone(),
                (None, p) => format!("{p}.{path}"),
            };
            let found = self.modules.contains_key(&key)
                || match (&dep, here.as_str()) {
                    _ if from_std => self.load_stdlib(&path),
                    (Some(d), _) => self.load_package(d, &path[d.len() + 1..]),
                    (None, ".") => self.load_user(&path, imp.path.span),
                    (None, "std") => false,
                    (None, p) => {
                        let p = p.to_string();
                        self.load_package(&p, &path)
                    }
                };
            self.cur = name.to_string();
            let path = key;
            if found {
                self.index_module(imp.path.span, &path);
                self.module_deps.entry(name.to_string()).or_default().push(path.clone());
            }
            if !found {
                let d = if from_std {
                    let all: Vec<String> = super::stdlib::modules();
                    Diagnostic::error("E0220", format!("unknown module `{path}`"), imp.path.span)
                        .with_label("no such standard library module")
                        .with_help(format!("the standard library modules are: {}", all.join(", ")))
                } else {
                    let written = imp.path.dotted();
                    let (pkg, rel) = match &dep {
                        Some(d) => (d.clone(), written[d.len() + 1..].to_string()),
                        None => (here.clone(), written.clone()),
                    };
                    let file = format!("{}.ck", rel.replace('.', "/"));
                    let label = if pkg == "." {
                        format!("no file `{file}` beside this program")
                    } else {
                        format!("no file `{file}` in package `{pkg}`")
                    };
                    let d = Diagnostic::error("E0220", format!("unknown module `{written}`"), imp.path.span).with_label(label);
                    if super::stdlib::source(&format!("std.{written}")).is_some() {
                        d.with_help(format!("the standard library's modules are under `std`: `import std.{written}`"))
                    } else {
                        d
                    }
                };
                self.err(d);
                self.import_failed(name, imp);
                continue;
            }
            if self.loading.contains(&path) && path != name {
                self.err(Diagnostic::error("E0222", format!("module `{path}` imports itself (import cycle)"), imp.path.span));
                continue;
            }
            // Referred to by its last component, unless renamed (D105).
            let last = path.rsplit('.').next().unwrap_or(&path).to_string();
            let qual = imp.alias.as_ref().map(|a| a.name.clone()).unwrap_or(last);
            let taken = self.modules[name].qualifiers.get(&qual).filter(|p| **p != path).cloned();
            if let Some(other) = taken {
                self.err(
                    Diagnostic::error("E0226", format!("two imports are both called `{qual}`"), imp.path.span)
                        .with_label(format!("`{qual}` already names `{other}`"))
                        .with_help(format!("rename one: `import {path} as {qual}_2`, with a name of your choice")),
                );
                continue;
            }
            self.modules.get_mut(name).unwrap().qualifiers.insert(qual, path.clone());
            if let Some(items) = &imp.items {
                for it in items {
                    let src = &self.modules[&path];
                    let t = src.exported_types.contains(&it.name).then(|| src.types[&it.name]);
                    let v = src.exported_values.contains(&it.name).then(|| src.values[&it.name]);
                    if t.is_none() && v.is_none() {
                        let mut d = Diagnostic::error(
                            "E0221",
                            format!("module `{path}` has no export named `{}`", it.name),
                            it.span,
                        );
                        if self.declares_privately(&path, &it.name) {
                            d = d.with_help(Self::private_help(&path, &it.name));
                        }
                        self.err(d);
                        continue;
                    }
                    // D36: importing a type imports its constructors.
                    let mut ctor_imports = Vec::new();
                    if let Some(Sym::Ty(tid)) = t {
                        let ti = &self.g.tys[tid.0 as usize];
                        if !ti.is_abstract {
                            for c in &ti.ctors {
                                ctor_imports.push((self.g.cons[c.0 as usize].name.to_string(), Sym::Con(*c)));
                            }
                        }
                    }
                    if let Some(s) = t.or(v) {
                        self.index_import(it.span, s);
                    }
                    let me = self.modules.get_mut(name).unwrap();
                    if let Some(t) = t {
                        me.import_types.insert(it.name.clone(), t);
                    }
                    if let Some(v) = v {
                        me.import_values.insert(it.name.clone(), v);
                    }
                    for (n, s) in ctor_imports {
                        me.import_values.insert(n, s);
                    }
                }
            }
        }
    }

    /// Remember that `imp` failed, so its qualifier's uses aren't reported again.
    fn import_failed(&mut self, module: &str, imp: &ast::Import) {
        let written = imp.path.dotted();
        let qual = imp.alias.as_ref().map(|a| a.name.clone()).unwrap_or_else(|| written.rsplit('.').next().unwrap_or("").to_string());
        self.modules.get_mut(module).unwrap().failed_imports.insert(qual);
    }

    /// The package module `m` belongs to: a dependency's name, `std`, or
    /// `.` for the program's own (D111).
    pub fn package_of(&self, m: &str) -> String {
        if m.starts_with("std.") {
            return "std".to_string();
        }
        self.module_pkg.get(m).cloned().unwrap_or_else(|| ".".to_string())
    }

    // ── name resolution ─────────────────────────────────────────────────────

    pub fn resolve(&self, name: &str, type_pos: bool) -> Option<Sym> {
        if name.starts_with('$') {
            if let Some(s) = self.generated_sym(name) {
                return Some(s);
            }
        }
        let m = self.module();
        let firsts = if type_pos { [&m.types, &m.import_types] } else { [&m.values, &m.import_values] };
        let seconds = if type_pos { [&m.values, &m.import_values] } else { [&m.types, &m.import_types] };
        for map in firsts.into_iter().chain(seconds) {
            if let Some(s) = map.get(name) {
                return Some(*s);
            }
        }
        if name == "Type" {
            return Some(Sym::Univ);
        }
        None
    }

    pub fn qualifier(&self, q: &str) -> Option<String> {
        self.module().qualifiers.get(q).cloned()
    }

    /// A module this one imports that declares `name` without exporting
    /// it, for a `help:` on an unknown or unexported name.
    pub fn private_in_imports(&self, name: &str) -> Option<String> {
        let mut imported: Vec<&String> = self.module().qualifiers.values().collect();
        imported.sort();
        imported.dedup();
        imported.into_iter().find(|m| self.declares_privately(m, name)).cloned()
    }

    /// `module` declares `name` and doesn't export it.
    pub fn declares_privately(&self, module: &str, name: &str) -> bool {
        self.modules.get(module).is_some_and(|m| {
            (m.values.contains_key(name) && !m.exported_values.contains(name))
                || (m.types.contains_key(name) && !m.exported_types.contains(name))
        })
    }

    /// The `help:` for a name `module` declares without exporting.
    pub fn private_help(module: &str, name: &str) -> String {
        format!("`{module}` declares `{name}` but doesn't export it; mark it `export` there to use it here")
    }

    pub fn resolve_qualified(&self, module: &str, name: &str, type_pos: bool) -> Option<Sym> {
        let m = self.modules.get(module)?;
        let t = m.exported_types.contains(name).then(|| m.types[name]);
        let v = m.exported_values.contains(name).then(|| m.values[name]);
        if type_pos {
            t.or(v)
        } else {
            v.or(t)
        }
    }

    // ── registration ────────────────────────────────────────────────────────

    fn declare(&mut self, name: &Ident, ty_ns: bool, sym: Sym, exported: bool) {
        let me = self.modules.get_mut(&self.cur).unwrap();
        let map = if ty_ns { &mut me.types } else { &mut me.values };
        if map.contains_key(&name.name) {
            let d = Diagnostic::error("E0350", format!("`{}` is defined twice in this module", name.name), name.span);
            self.err(d);
            return;
        }
        map.insert(name.name.clone(), sym);
        if exported {
            let me = self.modules.get_mut(&self.cur).unwrap();
            if ty_ns {
                me.exported_types.insert(name.name.clone());
            } else {
                me.exported_values.insert(name.name.clone());
            }
        }
    }

    /// Index a declaration: its name, and its header as written (for hover):
    /// up to the line its body starts on.
    fn index_header(&mut self, t: index::Target, name: Span, d: &ast::Decl) {
        // A declaration made by desugaring, with no name of its own (D136).
        if name.start == name.end {
            return;
        }
        let text = self.sources.get(&self.cur).map(|f| f.text.clone()).unwrap_or_default();
        let start = d.span.start as usize;
        let body = match &d.kind {
            DeclKind::Fn { body, decreasing, .. } => Some(decreasing.as_ref().map(|e| e.span.start).unwrap_or(body.span.start)),
            DeclKind::Lemma { lets, ensures, .. } => Some(lets.first().map(|l| l.0.span.start).unwrap_or(ensures.span.start)),
            DeclKind::Enum { ctors, .. } => ctors.first().map(|c| c.span.start),
            DeclKind::Record { fields, .. } => fields.first().map(|f| f.span.start),
            _ => None,
        };
        let end = match body {
            // Up to the start of the body's line, if it is on a later line.
            Some(b) => {
                let b = (b as usize).min(text.len());
                match text.get(start..b).and_then(|h| h.rfind('\n')) {
                    Some(k) => start + k,
                    None => b,
                }
            }
            None => (d.span.end as usize).min(text.len()),
        };
        // Without the comment lines between the header and the body (a
        // field's description, D128).
        let mut lines: Vec<&str> = text.get(start..end).unwrap_or("").lines().collect();
        while lines.len() > 1 && lines.last().is_some_and(|l| l.trim().is_empty() || l.trim_start().starts_with('#')) {
            lines.pop();
        }
        let header = lines.join("\n").trim_end().to_string();
        self.decl_sig.insert(t, header);
        self.index_decl(name, t);
    }

    pub(crate) fn new_def(&mut self, name: &str) -> DefId {
        self.g.defs.push(DefInfo {
            name: Rc::from(name),
            module: Rc::from(self.cur.as_str()),
            ty: Tm::Error,
            body: None,
            opaque: false,
            sealed: false,
            comptime: Vec::new(),
        });
        DefId(self.g.defs.len() as u32 - 1)
    }

    /// A new type: an `enum`'s or a `record`'s, its constructors to come.
    fn new_ty(&mut self, name: &Ident, params: &[ast::Param], is_record: bool, is_abstract: bool) -> TyId {
        self.g.tys.push(TyInfo {
            name: Rc::from(name.name.as_str()),
            module: Rc::from(self.cur.as_str()),
            params: Vec::new(),
            ctors: Vec::new(),
            is_record,
            is_abstract,
            positive: params.iter().map(|p| p.polarity == Some(ast::Polarity::Pos)).collect(),
            negative: params.iter().map(|p| p.polarity == Some(ast::Polarity::Neg)).collect(),
        });
        TyId(self.g.tys.len() as u32 - 1)
    }

    /// Allocate ids for every declaration; returns one entry per decl.
    fn register(&mut self, m: &ast::Module) -> Vec<Option<Sym>> {
        let mut ids = Vec::new();
        for (k_decl, d) in m.decls.iter().enumerate() {
            let exported = d.export != Export::No;
            let id = match &d.kind {
                // The prelude's `Type` is the universe itself (D132): its
                // declaration gives it a place and a description.
                DeclKind::Enum { name, ctors, .. }
                    if self.cur == "std.prelude" && name.name == "Type" && ctors.is_empty() && d.export == Export::Abstract =>
                {
                    self.declare(name, true, Sym::Univ, exported);
                    self.index_header(index::Target::Univ, name.span, d);
                    Some(Sym::Univ)
                }
                DeclKind::Enum { name, params, ctors, .. } => {
                    let abstract_ = d.export == Export::Abstract;
                    let tid = self.new_ty(name, params, false, abstract_);
                    self.declare(name, true, Sym::Ty(tid), exported);
                    self.index_header(index::Target::Ty(tid), name.span, d);
                    for (tag, c) in ctors.iter().enumerate() {
                        let cid = ConId(self.g.cons.len() as u32);
                        self.g.cons.push(ConInfo { name: Rc::from(c.name.name.as_str()), ty: tid, tag, fields: Vec::new() });
                        self.g.tys[tid.0 as usize].ctors.push(cid);
                        self.declare(&c.name, false, Sym::Con(cid), exported && !abstract_);
                        let text = format!("{}  (of `{}`)", self.src_text(c.span).trim(), name.name);
                        self.decl_sig.insert(index::Target::Con(cid), text);
                        self.index_decl(c.name.span, index::Target::Con(cid));
                        for (k, p) in c.params.iter().enumerate() {
                            self.index_decl(p.span, index::Target::Field(cid, k));
                        }
                    }
                    self.well_known(&name.name, tid);
                    Some(Sym::Ty(tid))
                }
                DeclKind::Record { name, params, .. } => {
                    let abstract_ = d.export == Export::Abstract;
                    let tid = self.new_ty(name, params, true, abstract_);
                    self.declare(name, true, Sym::Ty(tid), exported);
                    let cid = ConId(self.g.cons.len() as u32);
                    self.g.cons.push(ConInfo { name: Rc::from(name.name.as_str()), ty: tid, tag: 0, fields: Vec::new() });
                    self.g.tys[tid.0 as usize].ctors.push(cid);
                    // A class's dictionary is built only by instances (D136).
                    let is_class = matches!(self.decl_origin.get(k_decl), Some(super::classes::Origin::ClassRecord));
                    if !is_class {
                        self.declare(name, false, Sym::Con(cid), exported && !abstract_);
                    }
                    self.index_header(index::Target::Ty(tid), name.span, d);
                    {
                        let rec = name.name.clone();
                        self.decl_sig.insert(index::Target::Con(cid), self.decl_sig.get(&index::Target::Ty(tid)).cloned().unwrap_or_default());
                        self.decl_at.insert(index::Target::Con(cid), (self.cur.clone(), name.span));
                        if let DeclKind::Record { fields, .. } = &d.kind {
                            for f in fields {
                                let k = fields.iter().position(|g| g.name.name == f.name.name).unwrap_or(0);
                                let text = format!("{}  (field of `{rec}`)", self.src_text(f.span).trim());
                                self.decl_sig.insert(index::Target::Field(cid, k), text);
                                self.index_decl(f.name.span, index::Target::Field(cid, k));
                            }
                        }
                    }
                    self.well_known(&name.name, tid);
                    Some(Sym::Ty(tid))
                }
                DeclKind::Alias { name, .. } => {
                    let id = self.new_def(&name.name);
                    self.declare(name, true, Sym::Def(id), exported);
                    if self.cur == "std.prelude" {
                        use checkers_rt::array::Layout;
                        let layout = match name.name.as_str() {
                            "Nat" => {
                                self.g.well_known.nat = Some(id);
                                None
                            }
                            "Bytes" => {
                                self.g.well_known.bytes = Some(id);
                                None
                            }
                            "U8" => Some(Layout::U8),
                            "I8" => Some(Layout::I8),
                            "U16" => Some(Layout::U16),
                            "U32" | "Char" => Some(Layout::U32),
                            "I32" => Some(Layout::I32),
                            "U64" => Some(Layout::U64),
                            "I64" => Some(Layout::I64),
                            _ => None,
                        };
                        if let Some(l) = layout {
                            self.g.well_known.layouts.push((id, l as u8));
                        }
                    }
                    self.def_class.insert(id, "type");
                    self.index_header(index::Target::Def(id), name.span, d);
                    Some(Sym::Def(id))
                }
                DeclKind::Fn { name, .. } | DeclKind::Lemma { name, .. } | DeclKind::Const { name, .. } => {
                    let id = self.new_def(&name.name);
                    self.declare(name, false, Sym::Def(id), exported);
                    let class = match &d.kind {
                        DeclKind::Lemma { .. } => "lemma",
                        DeclKind::Const { .. } => "constant",
                        _ => "function",
                    };
                    self.def_class.insert(id, class);
                    self.index_header(index::Target::Def(id), name.span, d);
                    Some(Sym::Def(id))
                }
                DeclKind::Check { .. } | DeclKind::Class { .. } | DeclKind::Instance { .. } => None,
            };
            ids.push(id);
        }
        if self.cur == "std.prelude" {
            let me = self.modules.get_mut("std.prelude").unwrap();
            for (n, s) in [("len", Sym::Len), ("format", Sym::Format)] {
                me.values.insert(n.into(), s);
                me.exported_values.insert(n.into());
            }
        }
        ids
    }

    fn well_known(&mut self, name: &str, tid: TyId) {
        let wk = &mut self.g.well_known;
        let ctors = self.g.tys[tid.0 as usize].ctors.clone();
        match (self.cur.as_str(), name) {
            ("std.prelude", "Bool") => {
                wk.bool_ty = Some(tid);
                wk.false_con = ctors.first().copied();
                wk.true_con = ctors.get(1).copied();
            }
            ("std.prelude", "Int") => wk.int = Some(tid),
            ("std.prelude", "String") => wk.string = Some(tid),
            ("std.prelude", "Array") => wk.array = Some(tid),
            ("std.prelude", "List") => {
                wk.list = Some(tid);
                wk.nil = ctors.first().copied();
                wk.cons = ctors.get(1).copied();
            }
            ("std.prelude", "Option") => {
                wk.option = Some(tid);
                wk.none = ctors.first().copied();
                wk.some = ctors.get(1).copied();
            }
            ("std.prelude", "Result") => {
                wk.result = Some(tid);
                wk.ok = ctors.first().copied();
                wk.err = ctors.get(1).copied();
            }
            ("std.future", "Future") => wk.future = Some(tid),
            ("std.cown", "Cown") => wk.cown = Some(tid),
            ("std.cown", "Sched") => wk.sched = Some(tid),
            _ => {}
        }
    }

    /// `main` is `fn main args sys -> code : args~List String, sys~System,
    /// code~ExitCode` (D31; `code` may be a `Future ExitCode`): what isn't
    /// written is that, what is must agree (E0366).
    fn check_main(&mut self, sig: &Sig, at: Span) {
        let params: Vec<(Name, Val)> = (sig.n_implicit..sig.binders.len()).map(|k| (sig.binders[k].0.clone(), self.eval(&sig.cx, &sig.binders[k].3))).collect();
        let res = self.eval(&sig.cx, &sig.result);
        let mut wrong = self.main_mismatches(&sig.cx, &params, &sig.result_name, &res);
        if wrong.is_empty() {
            for p in sig.preds.iter().filter(|p| !p.is_post && p.alias.is_none()) {
                wrong.push(format!("`{}` is a precondition, which the runtime can't prove", p.text));
            }
        }
        self.report_main(wrong, at, None);
    }

    /// An exported `let main` (D181): its value's type must be D31's. The
    /// result is the value as a function of the two parameters the runtime
    /// passes, whatever computes it.
    fn check_main_const(&mut self, value: Tm, ty: &Val, at: Span) -> Tm {
        let mut cx = Cx::default();
        let mut params: Vec<(Name, Val)> = Vec::new();
        let mut mults = Vec::new();
        let mut cur = ty.clone();
        match self.force(ty) {
            Val::Error => return value,
            Val::Pi(..) => {}
            _ => {
                let shown = self.show_val(&cx, ty);
                let help = "declare it with `fn main args sys -> code`";
                self.report_main(vec![format!("`main` is `{shown}`, not a function")], at, Some(help));
                return value;
            }
        }
        while let Val::Pi(x, m, _, dom, c) = self.force(&cur) {
            let l = cx.lvl();
            cx.bind(&x, (*dom).clone(), m);
            params.push((x, (*dom).clone()));
            mults.push(m);
            cur = apply_closure(&self.g, &c, Val::var(l));
        }
        let mut wrong = self.main_mismatches(&cx, &params, "code", &cur);
        if wrong.is_empty() {
            for ((x, _), m) in params.iter().zip(&mults) {
                if *m == Mult::Zero {
                    wrong.push(format!("`{x}` is `ghost`, but the runtime passes it"));
                }
            }
        }
        if !wrong.is_empty() {
            self.report_main(wrong, at, None);
            return value;
        }
        let arg = |t: Tm, k: usize| Tm::App(Rc::new(t), Rc::new(Tm::Var(1 - k)), Icit::Expl, mults[k]);
        let body = arg(arg(value, 0), 1);
        params.iter().zip(&mults).rev().fold(body, |b, ((x, _), m)| Tm::Lam(x.clone(), *m, Icit::Expl, Rc::new(b)))
    }

    /// Does a value of type `v` have to satisfy a predicate, of `v` or of an
    /// alias it is defined with? `type Args = a~List String` only names its base.
    fn has_precondition(&self, v: &Val) -> bool {
        let mut v = crate::core::force_meta(&self.g, v.clone());
        loop {
            if self.refined_alias(&v).is_some_and(|(d, _)| !self.alias_preds[&d].is_empty()) {
                return true;
            }
            match crate::core::unfold(&self.g, &v) {
                Some(u) => v = crate::core::force_meta(&self.g, u),
                None => return false,
            }
        }
    }

    /// Each part of `main`'s parameters and result that isn't D31's.
    fn main_mismatches(&mut self, cx: &Cx, params: &[(Name, Val)], result_name: &str, res: &Val) -> Vec<String> {
        let ty = |e: &Self, m: &str, n: &str| e.g.tys.iter().position(|t| &*t.module == m && &*t.name == n).map(|i| Val::TyCon(TyId(i as u32), vec![]));
        let wk = self.g.well_known.clone();
        let (Some(system), Some(exit), Some(string), Some(list)) =
            (ty(self, "std.system", "System"), ty(self, "std.system", "ExitCode"), wk.string, wk.list)
        else {
            return Vec::new();
        };
        let args = Val::TyCon(list, vec![Val::TyCon(string, vec![])]);
        let lvl = cx.lvl();
        let mut wrong: Vec<String> = Vec::new();
        if params.len() != 2 {
            let plural = if params.len() == 1 { "" } else { "s" };
            wrong.push(format!("it takes {} parameter{plural}, not 2", params.len()));
        } else {
            for ((name, have), (want, shown)) in params.iter().zip([(args, "List String"), (system, "System")]) {
                if unify(&self.g, lvl, &want, have).is_err() {
                    let is = self.show_val(cx, have);
                    let why = if is == "Bool" { " (a name alone among the constraints is a condition, so a `Bool`)" } else { "" };
                    wrong.push(format!("`{name}` is `{is}`, not `{shown}`{why}"));
                } else if self.has_precondition(have) {
                    wrong.push(format!("`{name}` has a precondition, which the runtime can't prove"));
                }
            }
        }
        let future = wk.future.map(|f| Val::TyCon(f, vec![exit.clone()]));
        if unify(&self.g, lvl, &exit, res).is_err() && !future.is_some_and(|f| unify(&self.g, lvl, &f, res).is_ok()) {
            wrong.push(format!("`{result_name}` is `{}`, not `ExitCode`", self.show_val(cx, res)));
        }
        wrong
    }

    fn report_main(&mut self, wrong: Vec<String>, at: Span, help: Option<&str>) {
        let Some(first) = wrong.first() else { return };
        let mut d = Diagnostic::error("E0366", "this isn't `main`'s signature", at).with_label(first.clone());
        for w in &wrong[1..] {
            d = d.with_note(w.clone());
        }
        d = d.with_note("`main` is `fn main args sys -> code : args~List String, sys~System, code~ExitCode` (or a `Future ExitCode`); a type left out is that one");
        self.err(match help {
            Some(h) => d.with_help(h),
            None => d,
        });
    }

    // ── phases ──────────────────────────────────────────────────────────────

    fn typed_constraint<'a>(cs: &'a [Constraint], name: &str) -> Option<(&'a Expr, ast::Mult)> {
        cs.iter().find_map(|c| match c {
            Constraint::Typed { name: n, mult, ty } if n.name == name => Some((ty, *mult)),
            _ => None,
        })
    }

    pub fn mult_of(m: ast::Mult) -> Mult {
        match m {
            ast::Mult::Many => Mult::Many,
            ast::Mult::Ghost => Mult::Zero,
            ast::Mult::Own => Mult::One,
            ast::Mult::Comptime => Mult::Many,
        }
    }

    /// Elaborate an expression that must be a type.
    pub fn elab_type(&mut self, cx: &mut Cx, e: &Expr) -> Tm {
        // A tuple after `~` is a tuple type: each component is a type.
        if let ExprKind::Tuple(items) = &e.kind {
            return Tm::TupleTy(items.iter().map(|it| self.elab_type(cx, it)).collect());
        }
        let saved = cx.type_pos;
        cx.type_pos = true;
        self.in_spec += 1;
        let (t, ty) = self.infer(cx, e);
        self.in_spec -= 1;
        cx.type_pos = saved;
        match self.force(&ty) {
            Val::Univ(_) | Val::Error => t,
            Val::Neutral(Head::Meta(_), _) => {
                self.unify_at(cx, &Val::Univ(0), &ty, e.span, "this");
                t
            }
            other => {
                let shown = self.show_val(cx, &other);
                self.err(
                    Diagnostic::error("E0202", format!("expected a type, found a value of type `{shown}`"), e.span)
                        .with_help("after `~` write a type, such as `Nat` or `List String`"),
                );
                Tm::Error
            }
        }
    }

    /// Check a predicate (refinement, invariant, `ensures`) as `Bool`; it becomes
    /// part of a specification (§7.1).
    pub fn elab_pred(&mut self, cx: &mut Cx, e: &Expr, is_post: bool) -> Pred {
        let b = self.bool_ty();
        let saved = cx.type_pos;
        cx.type_pos = false;
        self.in_spec += 1;
        let tm = self.check(cx, e, &b, false);
        self.in_spec -= 1;
        cx.type_pos = saved;
        Pred { tm, text: self.src_text(e.span), span: e.span, is_post, alias: None }
    }

    fn phase_type_params(&mut self, m: &ast::Module, ids: &[Option<Sym>]) {
        for (d, id) in m.decls.iter().zip(ids) {
            let (params, cs) = match &d.kind {
                DeclKind::Enum { params, constraints, .. } | DeclKind::Record { params, constraints, .. } => {
                    (params, constraints)
                }
                _ => continue,
            };
            let Some(Sym::Ty(tid)) = id else { continue };
            self.g.fuel.set(DEFAULT_FUEL);
            let mut cx = Cx::default();
            let mut out = Vec::new();
            for p in params {
                let ty = match Self::typed_constraint(cs, &p.name.name) {
                    Some((e, _)) => self.elab_type(&mut cx, e),
                    None => Tm::Univ(0),
                };
                let v = self.eval(&cx, &ty);
                cx.bind(&p.name.name, v, Mult::Zero);
                out.push((Rc::from(p.name.name.as_str()), ty));
            }
            for c in cs {
                if let Constraint::Pred(e) = c {
                    self.elab_pred(&mut cx, e, false);
                }
            }
            self.g.tys[tid.0 as usize].params = out;
            self.solve_deferred();
        }
    }

    fn bind_type_params(&mut self, tid: TyId) -> Cx {
        let mut cx = Cx::default();
        let params = self.g.tys[tid.0 as usize].params.clone();
        for (n, t) in params {
            let v = self.eval(&cx, &t);
            cx.bind(&n, v, Mult::Zero);
        }
        cx
    }

    fn phase_aliases(&mut self, m: &ast::Module, ids: &[Option<Sym>]) {
        for (d, id) in m.decls.iter().zip(ids) {
            let DeclKind::Alias { params, constraints, .. } = &d.kind else { continue };
            let Some(Sym::Def(did)) = id else { continue };
            self.g.fuel.set(DEFAULT_FUEL);
            let mut cx = Cx::default();
            let mut ptys = Vec::new();
            // A parameter's type is what the alias's definition makes it
            // (`lo <= n` with `n~Int` makes `lo` an `Int`), and a type when
            // nothing decides.
            for p in params {
                let mt = self.fresh_meta(&cx);
                let mv = self.eval(&cx, &mt);
                cx.bind(&p.name, mv, Mult::Zero);
                ptys.push(mt);
            }
            let Some(Constraint::Typed { name, ty, .. }) = constraints.first() else {
                continue; // reported by the parser
            };
            let t = self.elab_type(&mut cx, ty);
            let tv = self.eval(&cx, &t);
            let l = cx.bind(&name.name, tv, Mult::Zero);
            self.bound_at(&mut cx, l, name.span);
            self.alias_subject.insert(*did, Rc::from(name.name.as_str()));
            for c in &constraints[1..] {
                match c {
                    Constraint::Pred(e) | Constraint::Named(_, e) => {
                        let p = self.elab_pred(&mut cx, e, false);
                        self.alias_preds.entry(*did).or_default().push(p);
                    }
                    Constraint::Typed { name, .. } => {
                        self.err(Diagnostic::error(
                            "E0351",
                            "a type alias has exactly one binder; the rest must be predicates",
                            name.span,
                        ));
                    }
                }
            }
            self.solve_deferred();
            let mut pty_terms = Vec::new();
            for (i, pt) in ptys.iter().enumerate() {
                let z = crate::core::zonk_metas(&self.g, i, pt);
                let h = z.head();
                if matches!(h, Tm::Meta(_)) {
                    let pv = crate::core::eval(&self.g, &Rc::new(cx.env[..i].to_vec()), pt);
                    let _ = crate::core::unify(&self.g, i, &pv, &Val::Univ(0));
                }
                pty_terms.push(crate::core::zonk_metas(&self.g, i, pt));
            }
            let mut body = t;
            let mut ty = Tm::Univ(0);
            for (p, pt) in params.iter().zip(pty_terms).rev() {
                body = Tm::Lam(Rc::from(p.name.as_str()), Mult::Zero, Icit::Expl, Rc::new(body));
                ty = Tm::Pi(Rc::from(p.name.as_str()), Mult::Zero, Icit::Expl, Rc::new(pt), Rc::new(ty));
            }
            let info = &mut self.g.defs[did.0 as usize];
            info.body = Some(body);
            info.ty = ty;
            self.solve_deferred();
        }
    }

    fn phase_ctors(&mut self, m: &ast::Module, ids: &[Option<Sym>]) {
        for (d, id) in m.decls.iter().zip(ids) {
            let Some(Sym::Ty(tid)) = id else { continue };
            let ctors = self.g.tys[tid.0 as usize].ctors.clone();
            match &d.kind {
                DeclKind::Enum { ctors: cs, .. } => {
                    for (c, cid) in cs.iter().zip(ctors) {
                        let names: Vec<&Ident> = c.params.iter().collect();
                        self.elab_fields(*tid, cid, &names, &c.constraints, &[]);
                    }
                }
                DeclKind::Record { fields, .. } => {
                    let names: Vec<&Ident> = fields.iter().map(|f| &f.name).collect();
                    let cs: Vec<Constraint> = fields
                        .iter()
                        .map(|f| Constraint::Typed {
                            name: f.name.clone(),
                            mult: f.mult,
                            ty: f.ty.clone(),
                        })
                        .collect();
                    let preds: Vec<&Expr> = fields.iter().flat_map(|f| f.preds.iter()).collect();
                    self.elab_fields(*tid, ctors[0], &names, &cs, &preds);
                }
                _ => {}
            }
        }
    }

    fn elab_fields(&mut self, tid: TyId, cid: ConId, names: &[&Ident], cs: &[Constraint], extra_preds: &[&Expr]) {
        self.g.fuel.set(DEFAULT_FUEL);
        let mut cx = self.bind_type_params(tid);
        let mut fields: Vec<(Name, Mult, Icit, Tm)> = Vec::new();
        let mut invs: Vec<FieldInv> = Vec::new();
        // Auto-bound implicit fields (D10), e.g. `m` in `xs~Vec a m`.
        let declared: HashSet<String> = names.iter().map(|n| n.name.clone()).collect();
        let mut autos = Vec::new();
        for c in cs {
            if let Constraint::Typed { ty, .. } = c {
                self.collect_free(&cx, ty, &declared, &mut autos);
            }
        }
        for a in &autos {
            let mv = self.fresh_meta(&cx);
            let v = self.eval(&cx, &mv);
            cx.bind(a, v, Mult::Zero);
            fields.push((Rc::from(a.as_str()), Mult::Zero, Icit::Impl, mv));
        }
        for n in names {
            let (ty, mult) = match Self::typed_constraint(cs, &n.name) {
                Some((e, m)) => {
                    let ty = self.elab_type(&mut cx, e);
                    let mult = Self::mult_of(m);
                    if mult == Mult::One {
                        self.check_own(&cx, &ty, e.span);
                    }
                    (ty, mult)
                }
                None => {
                    self.err(
                        Diagnostic::error("E0352", format!("constructor field `{}` needs a type", n.name), n.span)
                            .with_help(format!("add a constraint such as `{}~Nat`", n.name)),
                    );
                    (Tm::Error, Mult::Many)
                }
            };
            // A class function's `own` and `ghost` parameters (D156 i).
            let key = {
                let ti = &self.g.tys[tid.0 as usize];
                format!("{}.{}.{}", ti.module, ti.name, n.name)
            };
            let ty = match self.class_mults.get(&key) {
                Some(mults) => mult_params(&ty, mults),
                None => ty,
            };
            let v = self.eval(&cx, &ty);
            let at = cx.lvl();
            let l = cx.bind(&n.name, v, mult);
            cx.locals[l].span = Some(n.span);
            // A refinement-alias field type is an invariant (§7.1).
            for (fact, text, alias) in self.alias_facts(&cx, at, &ty, Val::var(l)) {
                let tm = quote(&self.g, cx.lvl(), &fact);
                invs.push((tm, text, n.span, cx.lvl(), Some((at, alias))));
            }
            fields.push((Rc::from(n.name.as_str()), mult, Icit::Expl, ty));
        }
        // Each condition may rely on those before it, as a signature's do
        // (fields' types are facts already through their locals).
        for c in cs {
            match c {
                Constraint::Pred(e) | Constraint::Named(_, e) => {
                    let p = self.elab_pred(&mut cx, e, false);
                    let v = self.eval(&cx, &p.tm);
                    cx.assume(v);
                    invs.push((p.tm, p.text, p.span, cx.lvl(), None));
                }
                Constraint::Typed { name, .. } if !declared.contains(&name.name) => {
                    self.err(Diagnostic::error(
                        "E0353",
                        format!("`{}` is not a field of this constructor", name.name),
                        name.span,
                    ));
                }
                _ => {}
            }
        }
        for e in extra_preds {
            let p = self.elab_pred(&mut cx, e, false);
            let v = self.eval(&cx, &p.tm);
            cx.assume(v);
            invs.push((p.tm, p.text, p.span, cx.lvl(), None));
        }
        // Every invariant as a term over params ++ fields.
        let total = cx.lvl();
        let preds: Vec<Pred> = invs
            .into_iter()
            .map(|(tm, text, span, lvl, alias)| {
                let v = eval(&self.g, &Rc::new(cx.env[..lvl].to_vec()), &tm);
                // A field's refinement alias, by its position among params ++ fields.
                Pred { tm: quote(&self.g, total, &v), text, span, is_post: false, alias }
            })
            .collect();
        if !preds.is_empty() {
            self.con_invs.insert(cid, preds);
        }
        self.solve_deferred();
        // Default auto-bound field types that weren't determined to `Type`.
        for (i, f) in fields.iter().enumerate() {
            if f.2 == Icit::Impl {
                let lvl = self.g.arity_ty(tid) + i;
                let ty = cx.locals[lvl].ty.clone();
                if let Val::Neutral(Head::Meta(_), _) = self.force(&ty) {
                    let _ = unify(&self.g, lvl, &ty, &Val::Univ(0));
                }
            }
        }
        // Quote field types with solved metas.
        let np = self.g.arity_ty(tid);
        let mut out = Vec::new();
        for (i, (n, m, ic, _)) in fields.iter().enumerate() {
            let v = cx.locals[np + i].ty.clone();
            out.push((n.clone(), *m, *ic, quote(&self.g, np + i, &v)));
        }
        self.g.cons[cid.0 as usize].fields = out;
    }

    /// Free lower-case names in a type expression that are not declared,
    /// not in scope, and not globals: candidates for auto-binding (D10).
    pub fn collect_free(&self, cx: &Cx, e: &Expr, declared: &HashSet<String>, out: &mut Vec<String>) {
        match &e.kind {
            ExprKind::Var(n) => {
                if !declared.contains(n)
                    && cx.lookup(n).is_none()
                    && self.resolve(n, true).is_none()
                    && self.qualifier(n).is_none()
                    && !out.contains(n)
                    && n != "_"
                    && !Self::is_cursor(n)
                {
                    out.push(n.clone());
                }
            }
            ExprKind::App(a, b) | ExprKind::Arrow(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
                self.collect_free(cx, a, declared, out);
                self.collect_free(cx, b, declared, out);
            }
            ExprKind::Tuple(v) | ExprKind::List(v) => v.iter().for_each(|x| self.collect_free(cx, x, declared, out)),
            ExprKind::Neg(x) => self.collect_free(cx, x, declared, out),
            // A refinement binds its own names; its predicates name no types.
            ExprKind::Refine(r) => {
                let mut inner = declared.clone();
                inner.extend(r.binders());
                for t in r.types() {
                    self.collect_free(cx, t, &inner, out);
                }
            }
            ExprKind::Field(x, _) => {
                // `q.name` qualifies or projects; it never introduces a type variable `q`.
                if let ExprKind::Var(q) = &x.kind {
                    if !declared.contains(q) && cx.lookup(q).is_none() {
                        return;
                    }
                }
                self.collect_free(cx, x, declared, out)
            }
            _ => {}
        }
    }

    fn phase_positivity(&mut self, m: &ast::Module, ids: &[Option<Sym>]) {
        // Parameter polarity (used for nested occurrences, e.g. `List Json` inside `Json`).
        // Start optimistic and compute a fixpoint.
        let tys: Vec<TyId> = ids.iter().flatten().filter_map(|s| if let Sym::Ty(t) = s { Some(*t) } else { None }).collect();
        for t in &tys {
            if !self.g.tys[t.0 as usize].ctors.is_empty() {
                let np = self.g.arity_ty(*t);
                self.g.tys[t.0 as usize].positive = vec![true; np];
            }
        }
        let mut changed = true;
        while changed {
            changed = false;
            for t in &tys {
                let before = self.g.tys[t.0 as usize].positive.clone();
                self.compute_polarity(*t);
                if self.g.tys[t.0 as usize].positive != before {
                    changed = true;
                }
            }
        }
        self.check_polarity_marks(m, ids);
        let rejected = self.check_strict_positivity(m, ids);
        self.check_recursive_types_have_values(m, ids, &rejected);
    }

    /// E0367 (D183). A type already rejected by E0354 gets no second error.
    fn check_recursive_types_have_values(&mut self, m: &ast::Module, ids: &[Option<Sym>], rejected: &BTreeSet<TyId>) {
        let tys: Vec<TyId> = ids.iter().flatten().filter_map(|s| if let Sym::Ty(t) = s { Some(*t) } else { None }).collect();
        for (d, id) in m.decls.iter().zip(ids) {
            let Some(Sym::Ty(tid)) = id else { continue };
            if rejected.contains(tid) || self.has_values(*tid) || !self.is_recursive(*tid, &tys) {
                continue;
            }
            let ti = &self.g.tys[tid.0 as usize];
            let name = ti.name.clone();
            let help = if ti.is_record {
                format!("hold the recursive field in a type that can be empty, such as `Option {name}` or `List {name}`")
            } else {
                format!("add a constructor that needs no value of `{name}`, such as one with no fields")
            };
            self.err(
                Diagnostic::error("E0367", format!("`{name}` has no values: building one always needs a value of `{name}` first"), d.span)
                    .with_label("no constructor can build the first value")
                    .with_help(help),
            );
        }
    }

    /// Does `tid` reach itself through the field types of `tys`, the types
    /// of its module? A cycle can't leave the module that declares it.
    fn is_recursive(&self, tid: TyId, tys: &[TyId]) -> bool {
        let mentions = |from: TyId, to: TyId| {
            self.g.tys[from.0 as usize].ctors.iter().any(|c| self.g.cons[c.0 as usize].fields.iter().any(|f| occurs_ty(&f.3, to)))
        };
        let mut seen = BTreeSet::new();
        let mut stack = vec![tid];
        while let Some(from) = stack.pop() {
            for &to in tys {
                if mentions(from, to) {
                    if to == tid {
                        return true;
                    }
                    if seen.insert(to) {
                        stack.push(to);
                    }
                }
            }
        }
        false
    }

    /// Does `tid` have a value when each of its parameters has one? This is
    /// the least fixed point of `instance_has_values`: each pass may use what
    /// earlier passes found, and a pass that finds nothing new ends the search.
    fn has_values(&self, tid: TyId) -> bool {
        let root = (tid, vec![true; self.g.arity_ty(tid)]);
        let mut known = BTreeSet::new();
        loop {
            let before = known.len();
            let found = self.instance_has_values(&root, &mut known, &mut BTreeSet::new());
            if found || known.len() == before {
                return found;
            }
        }
    }

    /// One pass over a type at its arguments, each argument reduced to whether
    /// it has a value. That keeps the instances finite under polymorphic
    /// recursion (`Nested (a, a)` inside `Nested a`).
    fn instance_has_values(&self, inst: &TypeInstance, known: &mut BTreeSet<TypeInstance>, seen: &mut BTreeSet<TypeInstance>) -> bool {
        let ti = &self.g.tys[inst.0 .0 as usize];
        if ti.ctors.is_empty() {
            return ti.is_abstract;
        }
        if known.contains(inst) {
            return true;
        }
        if !seen.insert(inst.clone()) {
            return false;
        }
        let found = ti.ctors.iter().any(|c| {
            let mut env = inst.1.clone();
            self.g.cons[c.0 as usize].fields.iter().all(|(_, _, _, t)| {
                let ok = self.type_has_values(t, &env, known, seen);
                env.push(true);
                ok
            })
        });
        if found {
            known.insert(inst.clone());
        }
        found
    }

    /// `env` says, for each variable in scope, whether it has a value. A form
    /// that isn't a known type former counts as having one (D183 c).
    fn type_has_values(&self, t: &Tm, env: &[bool], known: &mut BTreeSet<TypeInstance>, seen: &mut BTreeSet<TypeInstance>) -> bool {
        match t.spine().0 {
            Tm::Var(i) if matches!(t, Tm::Var(_)) => env.len().checked_sub(1 + i).and_then(|l| env.get(l)).copied().unwrap_or(true),
            Tm::TupleTy(ts) => ts.iter().all(|a| self.type_has_values(a, env, known, seen)),
            Tm::Pi(_, _, _, a, b) => {
                let mut inner = env.to_vec();
                inner.push(true);
                self.is_empty_enum(a) || self.type_has_values(b, &inner, known, seen)
            }
            h @ (Tm::TyCon(id) | Tm::TyConApp(id, _)) => {
                let held = if let Tm::TyConApp(_, args) = h { args.as_slice() } else { &[] };
                let applied = t.spine().1;
                let mut args: Vec<bool> = held.iter().chain(applied.iter().map(|a| a.as_ref())).map(|a| self.type_has_values(a, env, known, seen)).collect();
                args.resize(self.g.arity_ty(*id), true);
                self.instance_has_values(&(*id, args), known, seen)
            }
            _ => true,
        }
    }

    fn is_empty_enum(&self, t: &Tm) -> bool {
        matches!(t.spine().0, Tm::TyCon(id) | Tm::TyConApp(id, _) if {
            let ti = &self.g.tys[id.0 as usize];
            ti.ctors.is_empty() && !ti.is_abstract
        })
    }

    /// D16: marks only on abstract types, each one true of the constructors;
    /// importers then see only the marks.
    fn check_polarity_marks(&mut self, m: &ast::Module, ids: &[Option<Sym>]) {
        for (d, id) in m.decls.iter().zip(ids) {
            let Some(Sym::Ty(tid)) = id else { continue };
            let params = match &d.kind {
                DeclKind::Enum { params, .. } | DeclKind::Record { params, .. } => params,
                _ => continue,
            };
            let ti = &self.g.tys[tid.0 as usize];
            let (name, abstract_, has_ctors) = (ti.name.clone(), ti.is_abstract, !ti.ctors.is_empty());
            if !abstract_ {
                for p in params {
                    if let Some(pol) = p.polarity {
                        let mark = if pol == ast::Polarity::Pos { "+" } else { "-" };
                        self.err(
                            Diagnostic::error("E0360", format!("`{mark}{}` marks the polarity of a parameter, but only abstract types are marked", p.name.name), p.name.span)
                                .with_label("not an abstract type")
                                .with_help(format!("remove the `{mark}`: the polarity of `{name}`'s parameters is worked out from its constructors")),
                        );
                    }
                }
                continue;
            }
            if has_ctors {
                let np = params.len();
                for (j, p) in params.iter().enumerate() {
                    let Some(pol) = p.polarity else { continue };
                    let ctors = self.g.tys[tid.0 as usize].ctors.clone();
                    'ctors: for c in ctors {
                        let fields = self.g.cons[c.0 as usize].fields.clone();
                        for (i, (fname, _, _, t)) in fields.iter().enumerate() {
                            let idx = np + i - 1 - j;
                            let ok = match pol {
                                ast::Polarity::Pos => self.var_positive(t, idx, true),
                                ast::Polarity::Neg => self.var_negative(t, idx, true),
                            };
                            if !ok {
                                let (mark, wrong) = if pol == ast::Polarity::Pos { ("+", "to the left of an `->`") } else { ("-", "in a positive position") };
                                self.err(
                                    Diagnostic::error("E0359", format!("`{name}` marks `{mark}{}`, but field `{fname}` has `{}` {wrong}", p.name.name, p.name.name), p.name.span)
                                        .with_label(format!("declared `{mark}` here"))
                                        .with_help("importers rely on the mark: change the field, or remove the mark"),
                                );
                                break 'ctors;
                            }
                        }
                    }
                }
            }
            // Importers, and the rest of this module, see only the marks.
            let ti = &mut self.g.tys[tid.0 as usize];
            ti.positive = params.iter().map(|p| p.polarity == Some(ast::Polarity::Pos)).collect();
            ti.negative = params.iter().map(|p| p.polarity == Some(ast::Polarity::Neg)).collect();
        }
    }

    fn compute_polarity(&mut self, tid: TyId) {
        {
            let tid = &tid;
            let np = self.g.arity_ty(*tid);
            let ctors = self.g.tys[tid.0 as usize].ctors.clone();
            if ctors.is_empty() {
                return; // abstract/builtin: declared polarity
            }
            let mut pos = vec![true; np];
            for c in &ctors {
                let fields = self.g.cons[c.0 as usize].fields.clone();
                for (i, (_, _, _, t)) in fields.iter().enumerate() {
                    for (p, slot) in pos.iter_mut().enumerate() {
                        // Var index of parameter p at depth np + i
                        let idx = np + i - 1 - p;
                        if !self.var_positive(t, idx, true) {
                            *slot = false;
                        }
                    }
                }
            }
            self.g.tys[tid.0 as usize].positive = pos;
        }
    }

    /// Strict positivity of each type in its own constructors. Gives the
    /// types that fail it.
    fn check_strict_positivity(&mut self, m: &ast::Module, ids: &[Option<Sym>]) -> BTreeSet<TyId> {
        let mut rejected = BTreeSet::new();
        for (d, id) in m.decls.iter().zip(ids) {
            let Some(Sym::Ty(tid)) = id else { continue };
            let ctors = self.g.tys[tid.0 as usize].ctors.clone();
            for c in ctors {
                let fields = self.g.cons[c.0 as usize].fields.clone();
                for (fi, (fname, _, _, t)) in fields.iter().enumerate() {
                    if !self.ty_positive(t, *tid) {
                        let name = self.g.tys[tid.0 as usize].name.clone();
                        let diag = if let Some(a) = self.assoc_holder(t, *tid) {
                            Diagnostic::error("E0354", format!("`{name}` occurs in field `{fname}` as the argument of `{a}`, a type each instance gives, which may use it in a negative position"), d.span)
                                .with_help(format!("a recursive type can't hold a class's type at itself: the instance's type isn't known while `{name}` is checked; write that type in the field"))
                        } else if let Some(f) = self.param_holder(t, *tid, &self.g.tys[tid.0 as usize].params.clone(), fi) {
                            Diagnostic::error("E0354", format!("`{name}` occurs in field `{fname}` as an argument of `{f}`, a parameter, which may use it in a negative position"), d.span)
                                .with_help(format!("a recursive type may appear only directly or as an argument of a type that holds only values of it, like `List`; `{f}` could be any type constructor, so nothing is known of how it uses its argument"))
                        } else { match self.unmarked_holder(t, *tid) {
                            // Inside a type constructor that doesn't promise positivity.
                            Some(h) => {
                                let hi = &self.g.tys[h.0 as usize];
                                let help = if hi.is_abstract {
                                    format!("a recursive type may appear only directly or in a parameter marked `+`; `{}`'s module can mark it `+` if `{}` only holds values of it", hi.name, hi.name)
                                } else {
                                    format!("a recursive type may appear only where it is strictly positive; `{}` uses that parameter to the left of an `->`", hi.name)
                                };
                                Diagnostic::error("E0354", format!("`{name}` occurs in field `{fname}` as an argument of `{}`, which may use it in a negative position", hi.name), d.span)
                                    .with_help(help)
                            }
                            None => Diagnostic::error("E0354", format!("`{name}` occurs in a negative position in field `{fname}`"), d.span)
                                .with_help("a type may not appear to the left of `->` in its own constructors; this would make the logic inconsistent"),
                        }};
                        self.err(diag);
                        rejected.insert(*tid);
                    }
                }
            }
        }
        rejected
    }

    /// Does variable `idx` occur in `t` only strictly positively (never to
    /// the left of an `->`)? `pos` is false under such an arrow.
    fn var_positive(&self, t: &Tm, idx: usize, pos: bool) -> bool {
        match t {
            Tm::Var(i) => pos || *i != idx,
            Tm::Pi(_, _, _, a, b) => !occurs_var(a, idx) && self.var_positive(b, idx + 1, pos),
            Tm::TyConApp(t2, args) => {
                let positive = self.g.tys[t2.0 as usize].positive.clone();
                args.iter().enumerate().all(|(k, a)| {
                    if positive.get(k).copied().unwrap_or(false) {
                        self.var_positive(a, idx, pos)
                    } else {
                        !occurs_var(a, idx)
                    }
                })
            }
            Tm::TupleTy(ts) => ts.iter().all(|a| self.var_positive(a, idx, pos)),
            // A type constructor parameter applied (M25) promises nothing
            // about its argument.
            Tm::App(..) => {
                let (h, args) = t.spine();
                self.var_positive(h, idx, pos) && args.iter().all(|a| !occurs_var(a, idx))
            }
            // A type computed by a `match` or an `if` may be any of its arms.
            Tm::Case(s, c) => !occurs_var(s, idx) && case_arms(c).all(|(n, b)| self.var_positive(b, idx + n, pos)),
            // Any other form promises nothing about what it holds.
            other => !occurs_var(other, idx),
        }
    }

    /// Does variable `idx` occur in `t` only negatively (D16 `-`)? `pos` is
    /// the polarity of the current position.
    fn var_negative(&self, t: &Tm, idx: usize, pos: bool) -> bool {
        match t {
            Tm::Var(i) => !pos || *i != idx,
            Tm::Pi(_, _, _, a, b) => self.var_negative(a, idx, !pos) && self.var_negative(b, idx + 1, pos),
            Tm::TyConApp(t2, args) => {
                let ti = &self.g.tys[t2.0 as usize];
                let (positive, negative) = (ti.positive.clone(), ti.negative.clone());
                args.iter().enumerate().all(|(k, a)| {
                    if positive.get(k).copied().unwrap_or(false) {
                        self.var_negative(a, idx, pos)
                    } else if negative.get(k).copied().unwrap_or(false) {
                        self.var_negative(a, idx, !pos)
                    } else {
                        !occurs_var(a, idx)
                    }
                })
            }
            Tm::TupleTy(ts) => ts.iter().all(|a| self.var_negative(a, idx, pos)),
            Tm::App(..) => {
                let (h, args) = t.spine();
                self.var_negative(h, idx, pos) && args.iter().all(|a| !occurs_var(a, idx))
            }
            Tm::Case(s, c) => !occurs_var(s, idx) && case_arms(c).all(|(n, b)| self.var_negative(b, idx + n, pos)),
            other => !occurs_var(other, idx),
        }
    }

    /// The type constructor parameter (M25) applied to an argument holding
    /// `me`, by name: `f` in `kids~f (Rose f a)`. `t` is a field type under
    /// the type's parameters and the constructor's earlier fields.
    fn param_holder(&self, t: &Tm, me: TyId, params: &[(Name, Tm)], field: usize) -> Option<String> {
        fn go(t: &Tm, me: TyId, depth: usize, params: &[(Name, Tm)], extra: usize) -> Option<String> {
            match t {
                Tm::App(..) => {
                    let (h, args) = t.spine();
                    if let Tm::Var(i) = h {
                        if args.iter().any(|a| occurs_ty(a, me)) {
                            // Its level among the type's parameters, if it is one.
                            let lvl = (depth + extra).checked_sub(1 + i)?;
                            return params.get(lvl).map(|p| p.0.to_string()).or_else(|| Some("a type constructor".into()));
                        }
                    }
                    args.iter().find_map(|a| go(a, me, depth, params, extra))
                }
                Tm::Pi(_, _, _, a, b) => go(a, me, depth, params, extra).or_else(|| go(b, me, depth + 1, params, extra)),
                Tm::TyConApp(_, args) => args.iter().find_map(|a| go(a, me, depth, params, extra)),
                Tm::TupleTy(ts) => ts.iter().find_map(|a| go(a, me, depth, params, extra)),
                _ => None,
            }
        }
        go(t, me, 0, params, params.len() + field)
    }

    /// A class's type (#133) at a type holding `me`: `Display.Options` in
    /// `List (Display.Options Tree)`.
    fn assoc_holder(&self, t: &Tm, me: TyId) -> Option<String> {
        if let (Tm::Def(d), args) = t.spine() {
            if self.g.assoc_field(*d).is_some() && args.first().is_some_and(|a| occurs_ty(a, me)) {
                return Some(self.g.defs[d.0 as usize].name.to_string());
            }
        }
        let mut found = None;
        t.any_sub(|x, _| {
            found = self.assoc_holder(x, me);
            found.is_some()
        });
        found
    }

    /// The type constructor that holds `me` in a parameter not known to be
    /// strictly positive, if that (rather than an `->`) is why `t` fails.
    fn unmarked_holder(&self, t: &Tm, me: TyId) -> Option<TyId> {
        match t {
            Tm::TyConApp(t2, args) if *t2 != me => {
                let positive = self.g.tys[t2.0 as usize].positive.clone();
                args.iter().enumerate().find_map(|(k, a)| {
                    if positive.get(k).copied().unwrap_or(false) {
                        self.unmarked_holder(a, me)
                    } else if occurs_ty(a, me) {
                        Some(*t2)
                    } else {
                        None
                    }
                })
            }
            Tm::Pi(_, _, _, a, b) if !occurs_ty(a, me) => self.unmarked_holder(b, me),
            Tm::TupleTy(ts) => ts.iter().find_map(|a| self.unmarked_holder(a, me)),
            _ => None,
        }
    }

    /// Does the type `me` occur in `t`, a field of one of its constructors,
    /// only strictly positively: never to the left of an `->`, however many
    /// (SPEC §3, D182)? The rule `var_positive` holds a parameter to.
    fn ty_positive(&self, t: &Tm, me: TyId) -> bool {
        match t {
            Tm::TyConApp(t2, args) if *t2 == me => args.iter().all(|a| !occurs_ty(a, me)),
            Tm::Pi(_, _, _, a, b) => !occurs_ty(a, me) && self.ty_positive(b, me),
            Tm::TyConApp(t2, args) => {
                let positive = self.g.tys[t2.0 as usize].positive.clone();
                args.iter().enumerate().all(|(k, a)| {
                    if positive.get(k).copied().unwrap_or(false) {
                        self.ty_positive(a, me)
                    } else {
                        !occurs_ty(a, me)
                    }
                })
            }
            Tm::TupleTy(ts) => ts.iter().all(|a| self.ty_positive(a, me)),
            Tm::App(..) => {
                let (h, args) = t.spine();
                self.ty_positive(h, me) && args.iter().all(|a| !occurs_ty(a, me))
            }
            // A type computed by a `match` or an `if` may be any of its arms.
            Tm::Case(s, c) => !occurs_ty(s, me) && case_arms(c).all(|(_, b)| self.ty_positive(b, me)),
            Tm::TyCon(_) => true,
            // Any other form promises nothing about what it holds.
            other => !occurs_ty(other, me),
        }
    }

    fn phase_consts(&mut self, m: &ast::Module, ids: &[Option<Sym>]) {
        for (d, id) in m.decls.iter().zip(ids) {
            let DeclKind::Const { name, value } = &d.kind else { continue };
            let Some(Sym::Def(did)) = id else { continue };
            self.g.fuel.set(DEFAULT_FUEL);
            let mut cx = Cx::default();
            let (mut t, ty) = self.infer(&mut cx, value);
            self.solve_deferred();
            if name.name == "main" && d.export != Export::No && self.root.as_deref() == Some(self.cur.as_str()) {
                t = self.check_main_const(t, &ty, name.span);
            }
            let tyt = quote(&self.g, 0, &ty);
            let t = crate::core::zonk_metas(&self.g, 0, &t);
            let info = &mut self.g.defs[did.0 as usize];
            info.ty = tyt;
            info.body = Some(t);
        }
    }

    /// Elaborate `fn name params -> result : constraints` into a context and Π-type.
    // The loop over binders also visits the result slot (`k == nb`).
    #[allow(clippy::needless_range_loop)]
    pub fn signature(&mut self, params: &[Ident], result: Option<&Ident>, cs: &[Constraint]) -> Sig {
        let mut cx = Cx::default();
        let mut binders = Vec::new();
        let mut declared: HashSet<String> = params.iter().map(|p| p.name.clone()).collect();
        if let Some(r) = result {
            declared.insert(r.name.clone());
        }
        let mut autos = Vec::new();
        // Class clauses (`Ord a`, D136): implicit parameters, the dictionaries.
        let class_clauses: Vec<&Expr> = cs
            .iter()
            .filter_map(|c| match c {
                Constraint::Pred(e) if self.class_clause(e).is_some() => Some(e),
                _ => None,
            })
            .collect();
        for c in cs {
            if let Constraint::Typed { ty, .. } = c {
                self.collect_free(&cx, ty, &declared, &mut autos);
            }
        }
        for e in &class_clauses {
            self.collect_free(&cx, e, &declared, &mut autos);
        }
        for a in &autos {
            // Applied to arguments (`f a`), it is a type constructor (M25).
            let arity = cs
                .iter()
                .filter_map(|c| match c {
                    Constraint::Typed { ty, .. } => Some(super::classes::applied_arity(ty, a)),
                    _ => None,
                })
                .max()
                .unwrap_or(0);
            let mv = if arity == 0 {
                self.fresh_meta(&cx)
            } else {
                let sp = Span { start: 0, end: 0 };
                let ty = |sp| Expr { kind: ExprKind::Con("Type".into()), span: sp };
                let mut kind = ty(sp);
                for _ in 0..arity {
                    kind = Expr { kind: ExprKind::Arrow(Box::new(ty(sp)), Box::new(kind)), span: sp };
                }
                self.elab_type(&mut cx, &kind)
            };
            let v = self.eval(&cx, &mv);
            cx.bind(a, v, Mult::Zero);
            binders.push((Rc::from(a.as_str()), Mult::Zero, Icit::Impl, mv));
        }
        for (k, e) in class_clauses.iter().enumerate() {
            let ty = self.elab_type(&mut cx, e);
            let v = self.eval(&cx, &ty);
            let name = format!("$d{k}");
            cx.bind(&name, v, Mult::Many);
            binders.push((Rc::from(name.as_str()), Mult::Many, Icit::Impl, ty));
        }
        let n_implicit = binders.len();
        let mut comptime = Vec::new();
        // A refinement may mention a later parameter (#102): the parameter's
        // type is elaborated without its refinements here, and with them once
        // every parameter is in scope.
        let mut late_exprs: Vec<(usize, &Expr)> = Vec::new();
        for (k, p) in params.iter().enumerate() {
            let (ty, mult, ct) = match Self::typed_constraint(cs, &p.name) {
                Some((e, m)) if params[k + 1..].iter().any(|q| q.name != p.name && mentions_free(e, &q.name)) => {
                    late_exprs.push((binders.len(), e));
                    // Its names are indexed when it is elaborated in full.
                    let saved = (self.index_of.take(), self.index_all.take());
                    let ty = self.elab_type(&mut cx, &strip_refinements(e));
                    (self.index_of, self.index_all) = saved;
                    let mult = Self::mult_of(m);
                    if mult == Mult::One {
                        self.check_own(&cx, &ty, e.span);
                    }
                    (ty, mult, m == ast::Mult::Comptime)
                }
                Some((e, m)) => {
                    let ty = self.elab_type(&mut cx, e);
                    let mult = Self::mult_of(m);
                    if mult == Mult::One {
                        self.check_own(&cx, &ty, e.span);
                    }
                    (ty, mult, m == ast::Mult::Comptime)
                }
                None => (self.fresh_meta(&cx), Mult::Many, false),
            };
            let v = self.eval(&cx, &ty);
            let l = cx.bind(&p.name, v, mult);
            cx.locals[l].param = Some(k);
            self.bound_at(&mut cx, l, p.span);
            if ct {
                cx.locals[l].comptime = true;
                comptime.push(binders.len());
            }
            binders.push((Rc::from(p.name.as_str()), mult, Icit::Expl, ty));
        }
        let mut late = Vec::new();
        for (b, e) in late_exprs {
            let full = self.elab_type(&mut cx, e);
            let nb = binders.len();
            // The same type as its base: unifying them solves what the
            // refinements' elaboration left open.
            let fv = self.eval(&cx, &full);
            let bv = self.eval(&cx, &rename_free(&binders[b].3, 0, &|i| i + (nb - b)));
            let _ = unify(&self.g, cx.lvl(), &fv, &bv);
            let full = crate::core::zonk_metas(&self.g, nb, &full);
            let mut free = std::collections::BTreeSet::new();
            free_vars(&full, 0, &mut free);
            let deps: Vec<usize> = free.iter().map(|i| nb - 1 - i).filter(|j| *j > b).collect();
            cx.locals[b].refined = Some(self.eval(&cx, &full));
            late.push(Late { binder: b, ty: full, deps, n: nb });
        }
        let result_ty = match result.and_then(|r| Self::typed_constraint(cs, &r.name)) {
            Some((e, _)) => self.elab_type(&mut cx, e),
            // Not written: the same type at every call, so it may mention the
            // type parameters but not the values (`fib (x - 1) + fib (x - 2)`).
            None => self.fresh_meta_over_types(&cx),
        };
        for c in cs {
            if let Constraint::Typed { name, .. } = c {
                if !declared.contains(&name.name) {
                    self.err(
                        Diagnostic::error(
                            "E0355",
                            format!("`{}` is not a parameter or the result", name.name),
                            name.span,
                        )
                        .with_help("constraints can only give types to names in the header"),
                    );
                }
            }
        }
        // Predicates may mention the result, so check them with it in scope.
        let rv = self.eval(&cx, &result_ty);
        let rname = result.map(|r| r.name.clone()).unwrap_or_else(|| "_result".to_string());
        let nb = binders.len();
        let rl = cx.bind(&rname, rv, Mult::Zero);
        if let Some(r) = result {
            self.bound_at(&mut cx, rl, r.span);
        }
        // Each name a constraint gives a type to (`x~Nat`) is a use of it.
        for c in cs {
            if let Constraint::Typed { name, .. } = c {
                if let Some(l) = cx.lookup(&name.name) {
                    self.index_local(&cx, l, name.span);
                }
            }
        }
        let mut preds = Vec::new();
        // Refinement-alias types on parameters (preconditions) and the result (postcondition).
        for k in 0..=nb {
            let (ty, span) = if k < nb {
                let span = params.iter().find(|p| *p.name == *binders[k].0).map(|p| p.span).unwrap_or_default();
                (binders[k].3.clone(), span)
            } else {
                (result_ty.clone(), result.map(|r| r.span).unwrap_or_default())
            };
            for (fact, text, alias) in self.alias_facts(&cx, k, &ty, Val::var(k)) {
                let tm = quote(&self.g, cx.lvl(), &fact);
                preds.push(Pred { tm, text, span, is_post: k == nb, alias: Some((k, alias)) });
            }
        }
        let _ = rl;
        // While the signature is elaborated, each condition is known to the
        // ones after it, so a call in one may rely on those before (M17);
        // the body gets its facts its own way, so these are dropped after.
        let facts_before = cx.facts.len();
        for p in &preds {
            let v = self.eval(&cx, &p.tm);
            cx.assume(v);
        }
        let mut hyps = Vec::new();
        for c in cs {
            if let Constraint::Pred(e) | Constraint::Named(_, e) = c {
                if class_clauses.iter().any(|x| std::ptr::eq(*x, e)) {
                    continue;
                }
                let is_post = result.is_some_and(|r| mentions(e, &r.name));
                let named = matches!(c, Constraint::Named(..));
                if let Constraint::Named(n, _) = c {
                    if is_post {
                        self.err(
                            Diagnostic::error("E0289", format!("`{}` names a postcondition; only preconditions are named", n.name), n.span)
                                .with_help("name a precondition, to use it in the body with `have`"),
                        );
                    }
                    if let Some(bad) = super::expr::negative_forall(e, true) {
                        self.err(
                            Diagnostic::error("E0289", "this `forall` would have to be assumed where the function is called", bad)
                                .with_label("a `forall` before `implies` or under `not`")
                                .with_help("make it a precondition of its own: `name: forall …`"),
                        );
                    }
                    hyps.push((n.name.clone(), preds.len()));
                }
                if named {
                    self.forall_ok += 1;
                }
                let p = self.elab_pred(&mut cx, e, is_post);
                if named {
                    self.forall_ok -= 1;
                }
                let v = self.eval(&cx, &p.tm);
                cx.assume(v);
                preds.push(p);
            }
        }
        cx.facts.truncate(facts_before);
        cx.pop();
        Sig { cx, binders, result: result_ty, n_implicit, preds, result_name: rname, comptime, hyps, late }
    }

    /// The preconditions of a signature's function parameters that relate
    /// their argument to another parameter: `k~(x~A -> B, pred … j … x …)`,
    /// explicit parameters counted. Termination reads one as a promise
    /// where `pred` is a membership (#102).
    pub fn elem_promises(&self, sig: &Sig) -> Vec<ElemPromise> {
        let nb = sig.binders.len();
        let mut out = Vec::new();
        for b in sig.n_implicit..nb {
            // The type and the number of binders it is over.
            let (ty, lvl) = match sig.late.iter().find(|l| l.binder == b) {
                Some(l) => (&l.ty, nb),
                None => (&sig.binders[b].3, b),
            };
            let Tm::Pi(_, _, Icit::Expl, dom, _) = ty else { continue };
            let (Tm::Def(alias), captured) = dom.spine() else { continue };
            let Some(preds) = self.alias_preds.get(alias) else { continue };
            for p in preds {
                for (pred, q, c, s) in pred_subject(&p.tm) {
                    // `Var(1 + q)` is the alias's captured local `captured.len() - 1 - q`.
                    let Some(cap) = captured.len().checked_sub(q + 1).and_then(|i| captured.get(i)) else { continue };
                    let Tm::Var(i) = &***cap else { continue };
                    let Some(level) = lvl.checked_sub(i + 1) else { continue };
                    if level >= sig.n_implicit && level != b {
                        out.push(ElemPromise { k: b - sig.n_implicit, j: level - sig.n_implicit, pred, c, s });
                    }
                }
            }
        }
        out
    }

    pub fn pi_of(binders: &[(Name, Mult, Icit, Tm)], result: Tm) -> Tm {
        let mut t = result;
        for (n, m, i, ty) in binders.iter().rev() {
            t = Tm::Pi(n.clone(), *m, *i, Rc::new(ty.clone()), Rc::new(t));
        }
        t
    }

    pub fn lam_of(binders: &[(Name, Mult, Icit, Tm)], body: Tm) -> Tm {
        let mut t = body;
        for (n, m, i, _) in binders.iter().rev() {
            t = Tm::Lam(n.clone(), *m, *i, Rc::new(t));
        }
        t
    }

    fn phase_signatures(&mut self, m: &ast::Module, ids: &[Option<Sym>]) -> HashMap<usize, Sig> {
        let mut sigs = HashMap::new();
        for (k, (d, id)) in m.decls.iter().zip(ids).enumerate() {
            let Some(Sym::Def(did)) = id else { continue };
            self.g.fuel.set(DEFAULT_FUEL);
            let sig = match &d.kind {
                DeclKind::Fn { name, params, result, constraints, partial, decreasing, body } => {
                    let mut sig = self.signature(params, result.as_ref(), constraints);
                    if name.name == "main" && d.export != Export::No && self.root.as_deref() == Some(self.cur.as_str()) {
                        self.check_main(&sig, name.span);
                    }
                    if let Some(m) = head_meta(&sig.result) {
                        self.result_metas.insert(m, *did);
                    }
                    if d.export == Export::Transparent {
                        self.transparent.insert(*did);
                    }
                    // Parameters of a resource type are `own` whether or not it is written (D39).
                    for k in sig.n_implicit..sig.binders.len() {
                        let b = &sig.binders[k];
                        if b.1 == Mult::Zero || !self.type_linear(&b.3) {
                            continue;
                        }
                        let name = b.0.to_string();
                        let span = params.iter().find(|p| p.name == name).map(|p| p.span).unwrap_or(d.span);
                        let shown = match sig.cx.locals.iter().position(|l| *l.name == name) {
                            Some(pos) => {
                                sig.cx.locals[pos].mult = Mult::One;
                                let ty = sig.cx.locals[pos].ty.clone();
                                self.show_resource(&sig.cx, &ty)
                            }
                            None => "resource".to_string(),
                        };
                        sig.binders[k].1 = Mult::One;
                        self.resource_vars.insert((*did, name), (span, shown));
                    }
                    let builtin = is_builtin(body);
                    if builtin && !self.stdlib_mode {
                        self.err(Diagnostic::error(
                            "E0356",
                            "`__builtin` bodies are only allowed in the standard library",
                            body.result.span,
                        ));
                    } else if builtin && checkers_rt::builtins::symbol(&format!("{}.{}", self.cur, name.name)).is_none() {
                        self.err(
                            Diagnostic::error(
                                "E0361",
                                format!("the runtime has no builtin `{}.{}`", self.cur, name.name),
                                body.result.span,
                            )
                            .with_label("no implementation in this `ckc`")
                            .with_help(format!(
                                "add it to `rt/src/builtins/{}.rs`, or give `{}` a body in Checkers",
                                self.cur.trim_start_matches("std.").replace('.', "/"),
                                name.name
                            )),
                        );
                    }
                    self.fn_meta.insert(
                        *did,
                        FnMeta {
                            name: name.name.clone(),
                            span: name.span,
                            partial: *partial,
                            decreasing: decreasing.is_some(),
                            is_fn: true,
                            params: params
                                .iter()
                                .zip(sig.binders.iter().skip(sig.n_implicit))
                                .map(|(p, b)| (p.name.clone(), b.1, p.span))
                                .collect(),
                            n_implicit: sig.n_implicit,
                            builtin,
                            result: result.as_ref().map(|r| r.name.clone()),
                        },
                    );
                    self.specs.insert(
                        *did,
                        Spec {
                            preds: sig.preds.clone(),
                            n_binders: sig.binders.len(),
                            n_implicit: sig.n_implicit,
                            late: sig.late.clone(),
                            elems: self.elem_promises(&sig),
                            ..Default::default()
                        },
                    );
                    sig
                }
                DeclKind::Lemma { name, params, constraints, decreasing, .. } => {
                    let sig = self.signature(params, None, constraints);
                    self.fn_meta.insert(
                        *did,
                        FnMeta {
                            name: name.name.clone(),
                            span: name.span,
                            is_fn: false,
                            decreasing: decreasing.is_some(),
                            params: params
                                .iter()
                                .zip(sig.binders.iter().skip(sig.n_implicit))
                                .map(|(p, b)| (p.name.clone(), b.1, p.span))
                                .collect(),
                            n_implicit: sig.n_implicit,
                            ..Default::default()
                        },
                    );
                    // A lemma returns `Unit`; its content is the `ensures` clause.
                    let u = Tm::TupleTy(vec![]);
                    let rv = self.eval(&sig.cx, &sig.result);
                    let uv = self.unit();
                    let _ = unify(&self.g, sig.cx.lvl(), &rv, &uv);
                    let _ = u;
                    sig
                }
                _ => continue,
            };
            let ty = Self::pi_of(&sig.binders, sig.result.clone());
            self.g.defs[did.0 as usize].ty = ty;
            if !sig.comptime.is_empty() {
                let (what, bad) = match &d.kind {
                    DeclKind::Fn { partial: true, .. } => ("a `partial` function", true),
                    DeclKind::Lemma { .. } => ("a lemma", true),
                    _ => ("", false),
                };
                if bad {
                    let span = match &d.kind {
                        DeclKind::Fn { name, .. } | DeclKind::Lemma { name, .. } => name.span,
                        _ => d.span,
                    };
                    let help = if what == "a lemma" {
                        "a lemma is never run, so its parameters need no stage; remove `comptime`"
                    } else {
                        "compile-time code must end: only total functions take `comptime` parameters"
                    };
                    self.err(Diagnostic::error("E0272", format!("{what} can't have `comptime` parameters"), span).with_help(help));
                } else {
                    self.g.defs[did.0 as usize].comptime = sig.comptime.clone();
                }
            }
            if let DeclKind::Fn { partial: true, .. } = &d.kind {
                self.g.defs[did.0 as usize].opaque = true;
            }
            sigs.insert(k, sig);
        }
        sigs
    }

    fn phase_bodies(&mut self, m: &ast::Module, ids: &[Option<Sym>], mut sigs: HashMap<usize, Sig>, checks: bool) {
        for (k, (d, id)) in m.decls.iter().zip(ids).enumerate() {
            self.g.fuel.set(DEFAULT_FUEL);
            // Completing (D142): only the body the cursor is in.
            if let Some((module, at)) = &self.completing {
                let here = *module == self.cur && d.span.start <= *at && *at <= d.span.end;
                if !here && matches!(d.kind, DeclKind::Fn { .. } | DeclKind::Lemma { .. }) {
                    continue;
                }
            }
            match &d.kind {
                DeclKind::Fn { body, decreasing, .. } => {
                    let Some(Sym::Def(did)) = id else { continue };
                    let Some(mut sig) = sigs.remove(&k) else { continue };
                    if is_builtin(body) {
                        let name = format!("{}.{}", self.cur, self.g.defs[did.0 as usize].name);
                        self.g.defs[did.0 as usize].body = None;
                        self.g.defs[did.0 as usize].opaque = true;
                        let _ = name;
                        continue;
                    }
                    self.cur_fn = Some(*did);
                    self.module_fns.push(*did);
                    self.body_fns.push(*did);
                    let rty = self.eval(&sig.cx, &sig.result);
                    self.assume_pres(&mut sig);
                    let posts: Vec<Pred> = sig.preds.iter().filter(|p| p.is_post).cloned().collect();
                    let fname = self.g.defs[did.0 as usize].name.to_string();
                    // A class's function: each instance proves its postconditions (D136).
                    let checked = !posts.is_empty() && !self.class_methods.contains(did);
                    self.post_target =
                        checked.then(|| PostTarget { posts, func: fname, binders: sig.cx.env.to_vec(), invariants: Vec::new() });
                    let _ = decreasing;
                    let bt = self.check_block(&mut sig.cx, body, &rty, true);
                    self.post_target = None;
                    self.solve_deferred();
                    self.report_unsolved_sig(*did, &sig, d.span);
                    // Dictionaries found after the body was checked (D136).
                    let full = crate::core::zonk_metas(&self.g, 0, &Self::lam_of(&sig.binders, bt));
                    crate::usage::check_fn(self, *did, &full);
                    self.g.defs[did.0 as usize].body = Some(full);
                    self.cur_fn = None;
                }
                DeclKind::Lemma { name, lets, ensures, proof, .. } => {
                    let Some(Sym::Def(did)) = id else { continue };
                    let Some(mut sig) = sigs.remove(&k) else { continue };
                    self.cur_fn = Some(*did);
                    self.module_fns.push(*did);
                    self.assume_pres(&mut sig);
                    self.lemma_lets(&mut sig.cx, lets);
                    self.forall_ok += 1;
                    let ens = self.elab_pred(&mut sig.cx, ensures, false);
                    self.forall_ok -= 1;
                    self.solve_deferred();
                    let goal = self.eval(&sig.cx, &ens.tm);
                    match proof {
                        None => {
                            let kind = ObKind::Lemma { name: name.name.clone() };
                            self.oblige(&sig.cx, ensures.span, kind, ens.text.clone(), goal, None);
                        }
                        Some(block) => {
                            // Concluding a `forall` (D146): its variables are
                            // in scope in the proof, its premises facts.
                            let goal = self.intro_forall(&mut sig.cx, &ens.tm, goal);
                            let saved = self.proof_goal.replace((goal, ens.text.clone()));
                            let unit = self.unit();
                            self.in_proof += 1;
                            let _ = self.check_block(&mut sig.cx, block, &unit, true);
                            self.in_proof -= 1;
                            self.proof_goal = saved;
                            self.solve_deferred();
                        }
                    }
                    self.cur_fn = None;
                }
                DeclKind::Check { expr } if checks => {
                    let mut cx = Cx::default();
                    let b = self.bool_ty();
                    self.last_eq_ty = None;
                    let t = self.check(&mut cx, expr, &b, false);
                    self.solve_deferred();
                    if let (Tm::PrimApp(Prim::Eq, _), Some(ty)) = (&t, self.last_eq_ty.take()) {
                        let ty = quote(&self.g, 0, &ty);
                        self.check_eq_tys.insert(expr.span, ty);
                    }
                    let t = crate::core::zonk_metas(&self.g, 0, &t);
                    self.checks.push((self.cur.clone(), expr.span, t));
                }
                _ => {}
            }
        }
        self.resolve_insts();
    }

    /// A lemma's statement (its `let`s and `ensures`), before any body, so a
    /// `have` may use a lemma declared later.
    fn phase_lemma_statements(&mut self, m: &ast::Module, ids: &[Option<Sym>], sigs: &mut HashMap<usize, Sig>) {
        for (k, (d, id)) in m.decls.iter().zip(ids).enumerate() {
            let DeclKind::Lemma { lets, ensures, decreasing, .. } = &d.kind else { continue };
            let Some(Sym::Def(did)) = id else { continue };
            let Some(sig) = sigs.get(&k) else { continue };
            self.g.fuel.set(DEFAULT_FUEL);
            let mut cx = sig.cx.clone();
            // The hypotheses are known while the conclusion is elaborated (M17).
            // They were elaborated with a (lemma-less) result in scope.
            let mut with_result = cx.clone();
            with_result.bind("_result", Val::Univ(0), Mult::Zero);
            let hyps: Vec<Val> = sig.preds.iter().map(|p| self.eval(&with_result, &p.tm)).collect();
            for v in hyps {
                cx.assume(v);
            }
            let lets_tm = self.lemma_lets(&mut cx, lets);
            // The induction's measure (#76), over the parameters and `let`s;
            // kept over the parameters alone, the `let`s replaced by their values.
            let measure = decreasing.as_ref().map(|e| {
                let saved = self.cur_fn.replace(*did);
                let comps = self.check_measure(&mut cx, e);
                self.solve_deferred();
                self.cur_fn = saved;
                let n = sig.binders.len();
                let comps = comps.iter().map(|t| quote(&self.g, n, &self.eval(&cx, t))).collect();
                (comps, self.src_text(e.span))
            });
            // A lemma may conclude a `forall` (D146), positively.
            if let Some(bad) = super::expr::negative_forall(ensures, true) {
                self.err(
                    Diagnostic::error("E0289", "this lemma would have to show a `forall` false, which takes a value it fails for", bad)
                        .with_label("a `forall` before `implies` or under `not`")
                        .with_help("conclude what holds of that value instead"),
                );
            }
            self.forall_ok += 1;
            let ens = self.elab_pred(&mut cx, ensures, true);
            self.forall_ok -= 1;
            self.solve_deferred();
            let spec = Spec {
                preds: sig.preds.clone(),
                n_binders: sig.binders.len(),
                n_implicit: sig.n_implicit,
                lets: lets_tm,
                ensures: Some(ens),
                measure,
                late: sig.late.clone(),
                elems: Vec::new(),
            };
            self.specs.insert(*did, spec);
        }
    }

    /// Elaborate a lemma's header `let`s into `cx`, returning their terms.
    fn lemma_lets(&mut self, cx: &mut Cx, lets: &[(ast::Pattern, Expr)]) -> Vec<Tm> {
        let mut out = Vec::new();
        for (p, e) in lets {
            self.in_spec += 1;
            let (t, ty) = self.infer(cx, e);
            self.in_spec -= 1;
            match &p.kind {
                ast::PatKind::Var(n) => {
                    let v = self.eval(cx, &t);
                    cx.define(n, ty, v, Mult::Zero);
                    out.push(t);
                }
                _ => {
                    self.err(Diagnostic::error("E0357", "`let` in a lemma header binds a single name", p.span));
                }
            }
        }
        out
    }

    /// The preconditions are facts in the body (§7.1).
    fn assume_pres(&mut self, sig: &mut Sig) {
        let mut env = sig.cx.env.to_vec();
        env.push(Val::var(sig.cx.lvl())); // the result slot; preconditions don't mention it
        let env = Rc::new(env);
        self.cur_hyps.clear();
        for (k, p) in sig.preds.iter().enumerate().filter(|(_, p)| !p.is_post) {
            let v = eval(&self.g, &env, &p.tm);
            if let Some((n, _)) = sig.hyps.iter().find(|(_, i)| *i == k) {
                self.cur_hyps.push((n.clone(), v.clone()));
            }
            sig.cx.assume(v);
        }
    }

    /// Every function's `decreasing` measure, before any body, so calls to
    /// functions defined later can be checked against it (§5.3). A lemma's
    /// is checked with its statement, where its `let`s are in scope.
    fn phase_measures(&mut self, m: &ast::Module, ids: &[Option<Sym>], sigs: &HashMap<usize, Sig>) {
        for (k, (d, id)) in m.decls.iter().zip(ids).enumerate() {
            let DeclKind::Fn { decreasing: Some(e), .. } = &d.kind else { continue };
            let (Some(Sym::Def(did)), Some(sig)) = (id, sigs.get(&k)) else { continue };
            self.g.fuel.set(DEFAULT_FUEL);
            let mut sig = Sig {
                cx: sig.cx.clone(),
                binders: sig.binders.clone(),
                result: sig.result.clone(),
                n_implicit: sig.n_implicit,
                preds: sig.preds.clone(),
                result_name: sig.result_name.clone(),
                comptime: sig.comptime.clone(),
                hyps: sig.hyps.clone(),
                late: sig.late.clone(),
            };
            self.cur_fn = Some(*did);
            self.assume_pres(&mut sig);
            let comps = self.check_measure(&mut sig.cx, e);
            self.solve_deferred();
            let text = self.src_text(e.span);
            if let Some(spec) = self.specs.get_mut(did) {
                spec.measure = Some((comps, text));
            }
            self.cur_fn = None;
        }
    }

    /// A measure: a `Nat`, or a tuple of `Nat`s compared lexicographically.
    fn check_measure(&mut self, cx: &mut Cx, e: &Expr) -> Vec<Tm> {
        let n = self.nat();
        match &e.kind {
            ExprKind::Tuple(items) => items.iter().map(|it| self.check(cx, it, &n, false)).collect(),
            _ => vec![self.check(cx, e, &n, false)],
        }
    }

    fn report_unsolved_sig(&mut self, did: DefId, sig: &Sig, span: Span) {
        let mut cx = Cx::default();
        for (n, m, _, t) in &sig.binders {
            let v = self.eval(&cx, t);
            if has_unsolved(&self.g, cx.lvl(), &v) {
                let fname = self.g.defs[did.0 as usize].name.clone();
                self.err(
                    Diagnostic::error(
                        "E0203",
                        format!("cannot infer the type of `{n}` in `{fname}`"),
                        span,
                    )
                    .with_help(format!("add a constraint such as `{n}~Nat` to the header")),
                );
                return;
            }
            cx.bind(n, v, *m);
        }
    }
}

fn is_builtin(b: &ast::Block) -> bool {
    b.stmts.is_empty() && matches!(&b.result.kind, ExprKind::Var(n) if n == "__builtin")
}

/// A type with the predicates of its refinements removed: `(x~a -> Bool,
/// p x)` is `(x~a -> Bool)`, the type a parameter has before the later
/// parameters its predicates mention are in scope (#102).
fn strip_refinements(e: &Expr) -> Expr {
    let go = |x: &Expr| Box::new(strip_refinements(x));
    let kind = match &e.kind {
        ExprKind::Refine(r) => ExprKind::Refine(Box::new(ast::RefineTy {
            param: r.param.clone(),
            own: r.own,
            dom: strip_refinements(&r.dom),
            arrow: r.arrow.as_ref().map(|(n, t)| (n.clone(), strip_refinements(t))),
            preds: Vec::new(),
        })),
        ExprKind::App(a, b) => ExprKind::App(go(a), go(b)),
        ExprKind::Arrow(a, b) => ExprKind::Arrow(go(a), go(b)),
        ExprKind::Tuple(xs) => ExprKind::Tuple(xs.iter().map(strip_refinements).collect()),
        ExprKind::List(xs) => ExprKind::List(xs.iter().map(strip_refinements).collect()),
        ExprKind::Par(xs) => ExprKind::Par(xs.iter().map(strip_refinements).collect()),
        k => k.clone(),
    };
    Expr { kind, span: e.span }
}

/// Whether the type `e` mentions `name` where a refinement's own names
/// (`x` of `(x~Int -> Int, x >= 5)`) don't hide it.
pub(crate) fn mentions_free(e: &Expr, name: &str) -> bool {
    match &e.kind {
        ExprKind::Var(n) => n == name,
        ExprKind::Refine(r) => {
            if r.types().into_iter().take(1).any(|t| mentions_free(t, name)) {
                return true;
            }
            // The result type is in the parameter's scope; the predicates
            // in both names' scopes.
            let bound = r.binders();
            if r.param.as_ref().is_some_and(|p| p.name == name) {
                return false;
            }
            if r.arrow.as_ref().is_some_and(|(_, t)| mentions_free(t, name)) {
                return true;
            }
            !bound.iter().any(|b| b == name) && r.preds.iter().any(|p| mentions(p, name))
        }
        ExprKind::App(a, b) | ExprKind::Arrow(a, b) => mentions_free(a, name) || mentions_free(b, name),
        ExprKind::Tuple(v) | ExprKind::List(v) | ExprKind::Par(v) => v.iter().any(|x| mentions_free(x, name)),
        _ => mentions(e, name),
    }
}

fn mentions(e: &Expr, name: &str) -> bool {
    let mut found = false;
    walk(e, &mut |x| {
        if let ExprKind::Var(n) = &x.kind {
            if n == name {
                found = true;
            }
        }
    });
    found
}

fn walk(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    match &e.kind {
        ExprKind::App(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Arrow(a, b) | ExprKind::Index(a, b) => {
            walk(a, f);
            walk(b, f);
        }
        ExprKind::Tuple(v) | ExprKind::List(v) | ExprKind::Par(v) => v.iter().for_each(|x| walk(x, f)),
        ExprKind::Neg(x) | ExprKind::SectionL(_, x) | ExprKind::SectionR(_, x) | ExprKind::Try(x) | ExprKind::Field(x, _) => {
            walk(x, f)
        }
        ExprKind::If(a, b, c) => {
            walk(a, f);
            walk(b, f);
            walk(c, f);
        }
        ExprKind::Refine(r) => {
            r.types().into_iter().for_each(|t| walk(t, f));
            r.preds.iter().for_each(|p| walk(p, f));
        }
        _ => {}
    }
}

/// Does variable `idx` occur anywhere in `t`?
pub fn occurs_var(t: &Tm, idx: usize) -> bool {
    match t {
        Tm::Var(i) => *i == idx,
        _ => t.any_sub(|x, n| occurs_var(x, idx + n)),
    }
}

/// Does the type `me` occur anywhere in `t`?
pub fn occurs_ty(t: &Tm, me: TyId) -> bool {
    matches!(t, Tm::TyCon(x) | Tm::TyConApp(x, _) if *x == me) || t.any_sub(|x, _| occurs_ty(x, me))
}

pub fn has_unsolved(g: &Globals, l: usize, v: &Val) -> bool {
    has_meta(&quote(g, l, v))
}

pub(super) fn decl_name(d: &ast::Decl) -> Option<&Ident> {
    match &d.kind {
        DeclKind::Fn { name, .. }
        | DeclKind::Lemma { name, .. }
        | DeclKind::Const { name, .. }
        | DeclKind::Enum { name, .. }
        | DeclKind::Record { name, .. }
        | DeclKind::Alias { name, .. }
        | DeclKind::Class { name, .. } => Some(name),
        DeclKind::Check { .. } | DeclKind::Instance { .. } => None,
    }
}

/// The meta at the head of a term, if any.
fn head_meta(t: &Tm) -> Option<MetaId> {
    match t {
        Tm::Meta(m) => Some(*m),
        Tm::App(f, ..) => head_meta(f),
        _ => None,
    }
}

/// A term's head and its arguments.
/// A `match`'s arms, each with the number of binders it is under.
fn case_arms(c: &CaseTm) -> impl Iterator<Item = (usize, &Tm)> {
    let branches = c.branches.iter().map(|(_, n, b)| (*n, b));
    branches.chain(c.lits.iter().map(|(_, b)| (0, b))).chain(c.default.iter().map(|b| (0, b)))
}

/// A class function's field type with its `own` and `ghost` parameters
/// marked: the explicit parameters after its implicit type parameters, in order.
fn mult_params(t: &Tm, mults: &[Mult]) -> Tm {
    match t {
        Tm::Pi(x, m, Icit::Impl, a, b) => Tm::Pi(x.clone(), *m, Icit::Impl, a.clone(), Rc::new(mult_params(b, mults))),
        Tm::Pi(x, m, i, a, b) if !mults.is_empty() => {
            let m = if mults[0] == Mult::Many { *m } else { mults[0] };
            Tm::Pi(x.clone(), m, *i, a.clone(), Rc::new(mult_params(b, &mults[1..])))
        }
        _ => t.clone(),
    }
}

/// `p` as a call `pred a0 a1 …` with the refinement's subject (`Var 0`) as
/// explicit argument `s` and a captured local (`Var (1 + q)`) as explicit
/// argument `c`: each such `(pred, q, c, s)` (#102).
fn pred_subject(p: &Tm) -> Vec<(DefId, usize, usize, usize)> {
    let mut h = p;
    let mut expl = Vec::new();
    while let Tm::App(f, a, i, _) = h {
        if *i == Icit::Expl {
            expl.push(&**a);
        }
        h = f;
    }
    expl.reverse();
    let Tm::Def(d) = h else { return Vec::new() };
    let mut out = Vec::new();
    for (s, x) in expl.iter().enumerate() {
        if !matches!(x, Tm::Var(0)) {
            continue;
        }
        for (c, e) in expl.iter().enumerate() {
            if let Tm::Var(e) = e {
                if *e >= 1 {
                    out.push((*d, e - 1, c, s));
                }
            }
        }
    }
    out
}
