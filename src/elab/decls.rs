//! Modules, imports, and declarations.

use super::*;
use crate::syntax::ast::{Constraint, DeclKind, Export, Expr, ExprKind, Ident};

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
        self.cur = name.to_string();
        self.stdlib_mode = is_stdlib;
        let ids = self.register(m);
        self.decl_spans.insert(name.to_string(), m.decls.iter().zip(&ids).map(|(d, id)| (d.span, *id)).collect());
        self.phase_type_params(m, &ids);
        // Declarations in the order of what they use, not of the file (D65).
        let plan = super::order::plan(m);
        for chain in &plan.cycles {
            let name = |k: usize| decl_name(&m.decls[k]).map(|n| n.name.clone()).unwrap_or_default();
            let span = decl_name(&m.decls[chain[0]]).map(|n| n.span).unwrap_or(m.decls[chain[0]].span);
            let shown: Vec<String> = chain.iter().map(|k| format!("`{}`", name(*k))).collect();
            let msg = if chain.len() <= 2 {
                format!("`{}` depends on itself", name(chain[0]))
            } else {
                format!("`{}` depends on itself: {}", name(chain[0]), shown.join(" → "))
            };
            self.err(Diagnostic::error("E0225", msg, span).with_help(
                "a type, signature or constant can't need its own value; break the chain (recursion between function bodies is fine)",
            ));
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
                        self.err(Diagnostic::error(
                            "E0221",
                            format!("module `{path}` has no export named `{}`", it.name),
                            it.span,
                        ));
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

    /// Allocate ids for every declaration; returns one entry per decl.
    fn register(&mut self, m: &ast::Module) -> Vec<Option<Sym>> {
        let mut ids = Vec::new();
        for d in &m.decls {
            let exported = d.export != Export::No;
            let id = match &d.kind {
                DeclKind::Enum { name, params, ctors, .. } => {
                    let tid = TyId(self.g.tys.len() as u32);
                    let abstract_ = d.export == Export::Abstract;
                    self.g.tys.push(TyInfo {
                        name: Rc::from(name.name.as_str()),
                        module: Rc::from(self.cur.as_str()),
                        params: Vec::new(),
                        ctors: Vec::new(),
                        is_record: false,
                        is_abstract: abstract_,
                        positive: params.iter().map(|p| p.polarity == Some(ast::Polarity::Pos)).collect(),
                        negative: params.iter().map(|p| p.polarity == Some(ast::Polarity::Neg)).collect(),
                    });
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
                    let tid = TyId(self.g.tys.len() as u32);
                    let abstract_ = d.export == Export::Abstract;
                    self.g.tys.push(TyInfo {
                        name: Rc::from(name.name.as_str()),
                        module: Rc::from(self.cur.as_str()),
                        params: Vec::new(),
                        ctors: Vec::new(),
                        is_record: true,
                        is_abstract: abstract_,
                        positive: params.iter().map(|p| p.polarity == Some(ast::Polarity::Pos)).collect(),
                        negative: params.iter().map(|p| p.polarity == Some(ast::Polarity::Neg)).collect(),
                    });
                    self.declare(name, true, Sym::Ty(tid), exported);
                    let cid = ConId(self.g.cons.len() as u32);
                    self.g.cons.push(ConInfo { name: Rc::from(name.name.as_str()), ty: tid, tag: 0, fields: Vec::new() });
                    self.g.tys[tid.0 as usize].ctors.push(cid);
                    self.declare(name, false, Sym::Con(cid), exported && !abstract_);
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
                    if self.cur == "std.prelude" && name.name == "Nat" {
                        self.g.well_known.nat = Some(id);
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
                DeclKind::Check { .. } => None,
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
            ("std.prelude", "Bytes") => wk.bytes = Some(tid),
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
            for p in params {
                cx.bind(&p.name, Val::Univ(0), Mult::Zero);
                ptys.push(Tm::Univ(0));
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
                    Constraint::Pred(e) => {
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
            let mut body = t;
            let mut ty = Tm::Univ(0);
            for p in params.iter().rev() {
                body = Tm::Lam(Rc::from(p.name.as_str()), Mult::Zero, Icit::Expl, Rc::new(body));
                ty = Tm::Pi(Rc::from(p.name.as_str()), Mult::Zero, Icit::Expl, Rc::new(Tm::Univ(0)), Rc::new(ty));
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
        for c in cs {
            match c {
                Constraint::Pred(e) => {
                    let p = self.elab_pred(&mut cx, e, false);
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
        self.check_strict_positivity(m, ids);
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
                                        .with_help("importers rely on the mark (D16): change the field, or remove the mark"),
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

    fn check_strict_positivity(&mut self, m: &ast::Module, ids: &[Option<Sym>]) {
        // Strict positivity of each type in its own constructors.
        for (d, id) in m.decls.iter().zip(ids) {
            let Some(Sym::Ty(tid)) = id else { continue };
            let ctors = self.g.tys[tid.0 as usize].ctors.clone();
            for c in ctors {
                let fields = self.g.cons[c.0 as usize].fields.clone();
                for (fname, _, _, t) in &fields {
                    if !self.ty_positive(t, *tid, true) {
                        let name = self.g.tys[tid.0 as usize].name.clone();
                        let diag = match self.unmarked_holder(t, *tid) {
                            // Inside a type constructor that doesn't promise positivity.
                            Some(h) => {
                                let hi = &self.g.tys[h.0 as usize];
                                let help = if hi.is_abstract {
                                    format!("a recursive type may appear only directly or in a parameter marked `+`; `{}`'s module can mark it `+` if `{}` only holds values of it (D16)", hi.name, hi.name)
                                } else {
                                    format!("a recursive type may appear only where it is strictly positive; `{}` uses that parameter to the left of an `->`", hi.name)
                                };
                                Diagnostic::error("E0354", format!("`{name}` occurs in field `{fname}` as an argument of `{}`, which may use it in a negative position", hi.name), d.span)
                                    .with_help(help)
                            }
                            None => Diagnostic::error("E0354", format!("`{name}` occurs in a negative position in field `{fname}`"), d.span)
                                .with_help("a type may not appear to the left of `->` in its own constructors; this would make the logic inconsistent"),
                        };
                        self.err(diag);
                    }
                }
            }
        }
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
            other => pos || !occurs_var(other, idx),
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
            other => !occurs_var(other, idx),
        }
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

    fn ty_positive(&self, t: &Tm, me: TyId, pos: bool) -> bool {
        match t {
            Tm::TyConApp(t2, args) if *t2 == me => pos && args.iter().all(|a| !occurs_ty(a, me)),
            Tm::Pi(_, _, _, a, b) => self.ty_positive(a, me, !pos) && self.ty_positive(b, me, pos),
            Tm::TyConApp(t2, args) => {
                let positive = self.g.tys[t2.0 as usize].positive.clone();
                args.iter().enumerate().all(|(k, a)| {
                    if positive.get(k).copied().unwrap_or(false) {
                        self.ty_positive(a, me, pos)
                    } else {
                        !occurs_ty(a, me)
                    }
                })
            }
            Tm::TupleTy(ts) => ts.iter().all(|a| self.ty_positive(a, me, pos)),
            other => pos || !occurs_ty(other, me),
        }
    }

    fn phase_consts(&mut self, m: &ast::Module, ids: &[Option<Sym>]) {
        for (d, id) in m.decls.iter().zip(ids) {
            let DeclKind::Const { value, .. } = &d.kind else { continue };
            let Some(Sym::Def(did)) = id else { continue };
            self.g.fuel.set(DEFAULT_FUEL);
            let mut cx = Cx::default();
            let (t, ty) = self.infer(&mut cx, value);
            self.solve_deferred();
            let tyt = quote(&self.g, 0, &ty);
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
        for c in cs {
            if let Constraint::Typed { ty, .. } = c {
                self.collect_free(&cx, ty, &declared, &mut autos);
            }
        }
        for a in &autos {
            let mv = self.fresh_meta(&cx);
            let v = self.eval(&cx, &mv);
            cx.bind(a, v, Mult::Zero);
            binders.push((Rc::from(a.as_str()), Mult::Zero, Icit::Impl, mv));
        }
        let n_implicit = autos.len();
        let mut comptime = Vec::new();
        for (k, p) in params.iter().enumerate() {
            let (ty, mult, ct) = match Self::typed_constraint(cs, &p.name) {
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
        let result_ty = match result.and_then(|r| Self::typed_constraint(cs, &r.name)) {
            Some((e, _)) => self.elab_type(&mut cx, e),
            None => self.fresh_meta(&cx),
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
        for c in cs {
            if let Constraint::Pred(e) = c {
                let is_post = result.is_some_and(|r| mentions(e, &r.name));
                let p = self.elab_pred(&mut cx, e, is_post);
                let v = self.eval(&cx, &p.tm);
                cx.assume(v);
                preds.push(p);
            }
        }
        cx.facts.truncate(facts_before);
        cx.pop();
        Sig { cx, binders, result: result_ty, n_implicit, preds, result_name: rname, comptime }
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
                    if let Some(m) = head_meta(&sig.result) {
                        self.result_metas.insert(m, *did);
                    }
                    if d.export == Export::Transparent {
                        self.transparent.insert(*did);
                    }
                    // Parameters of a resource type are `own` whether or not it is written (D39).
                    for k in sig.n_implicit..sig.binders.len() {
                        let b = &sig.binders[k];
                        if b.1 != Mult::Many || !self.type_linear(&b.3) {
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
                        Spec { preds: sig.preds.clone(), n_binders: sig.binders.len(), n_implicit: sig.n_implicit, ..Default::default() },
                    );
                    sig
                }
                DeclKind::Lemma { name, params, constraints, .. } => {
                    let sig = self.signature(params, None, constraints);
                    self.fn_meta.insert(
                        *did,
                        FnMeta {
                            name: name.name.clone(),
                            span: name.span,
                            is_fn: false,
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
                        "compile-time code must end (D61): only total functions take `comptime` parameters"
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
                    let rty = self.eval(&sig.cx, &sig.result);
                    self.assume_pres(&mut sig);
                    let posts: Vec<Pred> = sig.preds.iter().filter(|p| p.is_post).cloned().collect();
                    let fname = self.g.defs[did.0 as usize].name.to_string();
                    self.post_target =
                        (!posts.is_empty()).then(|| PostTarget { posts, func: fname, binders: sig.cx.env.clone(), invariants: Vec::new() });
                    let _ = decreasing;
                    let bt = self.check_block(&mut sig.cx, body, &rty, true);
                    self.post_target = None;
                    self.solve_deferred();
                    self.report_unsolved_sig(*did, &sig, d.span);
                    let full = Self::lam_of(&sig.binders, bt);
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
                    let ens = self.elab_pred(&mut sig.cx, ensures, false);
                    self.solve_deferred();
                    let goal = self.eval(&sig.cx, &ens.tm);
                    match proof {
                        None => {
                            let kind = ObKind::Lemma { name: name.name.clone() };
                            self.oblige(&sig.cx, ensures.span, kind, ens.text.clone(), goal, None);
                        }
                        Some(block) => {
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
            let DeclKind::Lemma { lets, ensures, .. } = &d.kind else { continue };
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
            let ens = self.elab_pred(&mut cx, ensures, true);
            self.solve_deferred();
            let spec = Spec {
                preds: sig.preds.clone(),
                n_binders: sig.binders.len(),
                n_implicit: sig.n_implicit,
                lets: lets_tm,
                ensures: Some(ens),
                measure: None,
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
        let mut env = sig.cx.env.clone();
        env.push(Val::var(sig.cx.lvl())); // the result slot; preconditions don't mention it
        let env = Rc::new(env);
        for p in sig.preds.iter().filter(|p| !p.is_post) {
            let v = eval(&self.g, &env, &p.tm);
            sig.cx.assume(v);
        }
    }

    /// Every function's `decreasing` measure, before any body, so calls to
    /// functions defined later can be checked against it (§5.3).
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

pub fn occurs_var(t: &Tm, idx: usize) -> bool {
    match t {
        Tm::Var(i) => *i == idx,
        Tm::Pi(_, _, _, a, b) => occurs_var(a, idx) || occurs_var(b, idx + 1),
        Tm::Lam(_, _, _, b) => occurs_var(b, idx + 1),
        Tm::App(a, b, _, _) => occurs_var(a, idx) || occurs_var(b, idx),
        Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => {
            v.iter().any(|a| occurs_var(a, idx))
        }
        Tm::Proj(a, _) | Tm::Field(a, _, _) => occurs_var(a, idx),
        Tm::Let(_, _, a, b, c) => occurs_var(a, idx) || occurs_var(b, idx) || occurs_var(c, idx + 1),
        _ => false,
    }
}

pub fn occurs_ty(t: &Tm, me: TyId) -> bool {
    match t {
        Tm::TyCon(x) => *x == me,
        Tm::TyConApp(x, v) => *x == me || v.iter().any(|a| occurs_ty(a, me)),
        Tm::Pi(_, _, _, a, b) => occurs_ty(a, me) || occurs_ty(b, me),
        Tm::Lam(_, _, _, b) => occurs_ty(b, me),
        Tm::App(a, b, _, _) => occurs_ty(a, me) || occurs_ty(b, me),
        Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => v.iter().any(|a| occurs_ty(a, me)),
        _ => false,
    }
}

pub fn has_unsolved(g: &Globals, l: usize, v: &Val) -> bool {
    fn tm(t: &Tm) -> bool {
        match t {
            Tm::Meta(_) => true,
            Tm::Pi(_, _, _, a, b) => tm(a) || tm(b),
            Tm::Lam(_, _, _, b) => tm(b),
            Tm::App(a, b, _, _) => tm(a) || tm(b),
            Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => v.iter().any(tm),
            Tm::Proj(a, _) | Tm::Field(a, _, _) => tm(a),
            _ => false,
        }
    }
    tm(&quote(g, l, v))
}

/// The definitions a term mentions.
fn defs_in(t: &Tm, out: &mut Vec<DefId>) {
    match t {
        Tm::Def(d) => out.push(*d),
        Tm::Pi(_, _, _, a, b) | Tm::App(a, b, ..) => {
            defs_in(a, out);
            defs_in(b, out);
        }
        Tm::Lam(_, _, _, b) | Tm::Proj(b, _) | Tm::Field(b, _, _) => defs_in(b, out),
        Tm::Let(_, _, a, b, c) => {
            defs_in(a, out);
            defs_in(b, out);
            defs_in(c, out);
        }
        Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => {
            v.iter().for_each(|x| defs_in(x, out))
        }
        Tm::Case(s, c) => {
            defs_in(s, out);
            c.branches.iter().for_each(|(_, _, b)| defs_in(b, out));
            c.lits.iter().for_each(|(_, b)| defs_in(b, out));
            if let Some(b) = &c.default {
                defs_in(b, out);
            }
        }
        _ => {}
    }
}

fn decl_name(d: &ast::Decl) -> Option<&Ident> {
    match &d.kind {
        DeclKind::Fn { name, .. }
        | DeclKind::Lemma { name, .. }
        | DeclKind::Const { name, .. }
        | DeclKind::Enum { name, .. }
        | DeclKind::Record { name, .. }
        | DeclKind::Alias { name, .. } => Some(name),
        DeclKind::Check { .. } => None,
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
