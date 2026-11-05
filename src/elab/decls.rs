//! Modules, imports, and declarations.

use super::*;
use crate::syntax::ast::{Constraint, DeclKind, Export, Expr, ExprKind, Ident};

/// Signature of a function or lemma, elaborated into a context.
pub struct Sig {
    pub cx: Cx,
    /// (name, mult, icit, type) for every binder, implicit ones first.
    pub binders: Vec<(Name, Mult, Icit, Tm)>,
    pub result: Tm,
    pub n_implicit: usize,
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
        self.phase_type_params(m, &ids);
        self.phase_aliases(m, &ids);
        self.phase_ctors(m, &ids);
        self.phase_positivity(m, &ids);
        self.phase_consts(m, &ids);
        let sigs = self.phase_signatures(m, &ids);
        self.phase_bodies(m, &ids, sigs);
        self.check_termination();
        self.loading.pop();
    }

    // ── imports ─────────────────────────────────────────────────────────────

    fn imports(&mut self, m: &ast::Module, name: &str) {
        if name != "prelude" {
            self.load_stdlib("prelude");
            let p = &self.modules["prelude"];
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
            let found = self.modules.contains_key(&path) || self.load_stdlib(&path);
            self.cur = name.to_string();
            if !found {
                self.err(
                    Diagnostic::error("E0220", format!("unknown module `{path}`"), imp.path.span)
                        .with_help("the standard library modules are: prelude, list, system, terminal, files, cown, future, bytes, string, char, utf8, decimal, cursor"),
                );
                continue;
            }
            if self.loading.contains(&path) && path != name {
                self.err(Diagnostic::error("E0222", format!("module `{path}` imports itself (import cycle)"), imp.path.span));
                continue;
            }
            let qual = imp.alias.as_ref().map(|a| a.name.clone()).unwrap_or_else(|| path.clone());
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

    fn new_def(&mut self, name: &str) -> DefId {
        self.g.defs.push(DefInfo {
            name: Rc::from(name),
            module: Rc::from(self.cur.as_str()),
            ty: Tm::Error,
            body: None,
            opaque: false,
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
                    });
                    self.declare(name, true, Sym::Ty(tid), exported);
                    for (tag, c) in ctors.iter().enumerate() {
                        let cid = ConId(self.g.cons.len() as u32);
                        self.g.cons.push(ConInfo { name: Rc::from(c.name.name.as_str()), ty: tid, tag, fields: Vec::new() });
                        self.g.tys[tid.0 as usize].ctors.push(cid);
                        self.declare(&c.name, false, Sym::Con(cid), exported && !abstract_);
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
                    });
                    self.declare(name, true, Sym::Ty(tid), exported);
                    let cid = ConId(self.g.cons.len() as u32);
                    self.g.cons.push(ConInfo { name: Rc::from(name.name.as_str()), ty: tid, tag: 0, fields: Vec::new() });
                    self.g.tys[tid.0 as usize].ctors.push(cid);
                    self.declare(name, false, Sym::Con(cid), exported && !abstract_);
                    self.well_known(&name.name, tid);
                    Some(Sym::Ty(tid))
                }
                DeclKind::Alias { name, .. } => {
                    let id = self.new_def(&name.name);
                    self.declare(name, true, Sym::Def(id), exported);
                    Some(Sym::Def(id))
                }
                DeclKind::Fn { name, .. } | DeclKind::Lemma { name, .. } | DeclKind::Const { name, .. } => {
                    let id = self.new_def(&name.name);
                    self.declare(name, false, Sym::Def(id), exported);
                    Some(Sym::Def(id))
                }
                DeclKind::Check { .. } => None,
            };
            ids.push(id);
        }
        if self.cur == "prelude" {
            let me = self.modules.get_mut("prelude").unwrap();
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
            ("prelude", "Bool") => {
                wk.bool_ty = Some(tid);
                wk.false_con = ctors.first().copied();
                wk.true_con = ctors.get(1).copied();
            }
            ("prelude", "Nat") => wk.nat = Some(tid),
            ("prelude", "Int") => wk.int = Some(tid),
            ("prelude", "String") => wk.string = Some(tid),
            ("prelude", "Bytes") => wk.bytes = Some(tid),
            ("prelude", "List") => {
                wk.list = Some(tid);
                wk.nil = ctors.first().copied();
                wk.cons = ctors.get(1).copied();
            }
            ("prelude", "Option") => {
                wk.option = Some(tid);
                wk.none = ctors.first().copied();
                wk.some = ctors.get(1).copied();
            }
            ("prelude", "Result") => {
                wk.result = Some(tid);
                wk.ok = ctors.first().copied();
                wk.err = ctors.get(1).copied();
            }
            ("future", "Future") => wk.future = Some(tid),
            ("cown", "Cown") => wk.cown = Some(tid),
            ("cown", "Sched") => wk.sched = Some(tid),
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
        let (t, ty) = self.infer(cx, e);
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

    /// Check a predicate (refinement, invariant, `ensures`) as `Bool` and record it for the prover.
    pub fn elab_pred(&mut self, cx: &mut Cx, e: &Expr, what: &'static str) {
        let b = self.bool_ty();
        let saved = cx.type_pos;
        cx.type_pos = false;
        self.check(cx, e, &b, false);
        cx.type_pos = saved;
        self.obligations.push(Obligation { module: self.cur.clone(), span: e.span, what });
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
                    self.elab_pred(&mut cx, e, "type parameter constraint");
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
            cx.bind(&name.name, tv, Mult::Zero);
            for c in &constraints[1..] {
                match c {
                    Constraint::Pred(e) => self.elab_pred(&mut cx, e, "refinement"),
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
                Some((e, m)) => (self.elab_type(&mut cx, e), Self::mult_of(m)),
                None => {
                    self.err(
                        Diagnostic::error("E0352", format!("constructor field `{}` needs a type", n.name), n.span)
                            .with_help(format!("add a constraint such as `{}~Nat`", n.name)),
                    );
                    (Tm::Error, Mult::Many)
                }
            };
            let v = self.eval(&cx, &ty);
            cx.bind(&n.name, v, mult);
            fields.push((Rc::from(n.name.as_str()), mult, Icit::Expl, ty));
        }
        for c in cs {
            match c {
                Constraint::Pred(e) => self.elab_pred(&mut cx, e, "constructor invariant"),
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
            self.elab_pred(&mut cx, e, "field invariant");
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
        self.check_strict_positivity(m, ids);
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
                        self.err(
                            Diagnostic::error(
                                "E0354",
                                format!("`{name}` occurs in a negative position in field `{fname}`"),
                                d.span,
                            )
                            .with_help("a type may not appear to the left of `->` in its own constructors; this would make the logic inconsistent"),
                        );
                    }
                }
            }
        }
    }

    fn var_positive(&self, t: &Tm, idx: usize, pos: bool) -> bool {
        match t {
            Tm::Var(i) => pos || *i != idx,
            Tm::Pi(_, _, _, a, b) => self.var_positive(a, idx, !pos) && self.var_positive(b, idx + 1, pos),
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
        for (k, p) in params.iter().enumerate() {
            let (ty, mult) = match Self::typed_constraint(cs, &p.name) {
                Some((e, m)) => (self.elab_type(&mut cx, e), Self::mult_of(m)),
                None => (self.fresh_meta(&cx), Mult::Many),
            };
            let v = self.eval(&cx, &ty);
            let l = cx.bind(&p.name, v, mult);
            cx.locals[l].param = Some(k);
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
        let has_preds = cs.iter().any(|c| matches!(c, Constraint::Pred(_)));
        if has_preds {
            let rv = self.eval(&cx, &result_ty);
            let rname = result.map(|r| r.name.as_str()).unwrap_or("_result");
            cx.bind(rname, rv, Mult::Zero);
            for c in cs {
                if let Constraint::Pred(e) = c {
                    let what = if result.is_some_and(|r| mentions(e, &r.name)) { "postcondition" } else { "precondition" };
                    self.elab_pred(&mut cx, e, what);
                }
            }
            cx.pop();
        }
        Sig { cx, binders, result: result_ty, n_implicit }
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
                    let sig = self.signature(params, result.as_ref(), constraints);
                    let builtin = is_builtin(body);
                    if builtin && !self.stdlib_mode {
                        self.err(Diagnostic::error(
                            "E0356",
                            "`__builtin` bodies are only allowed in the standard library",
                            body.result.span,
                        ));
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
                        },
                    );
                    sig
                }
                DeclKind::Lemma { params, constraints, .. } => {
                    let sig = self.signature(params, None, constraints);
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
            if let DeclKind::Fn { partial: true, .. } = &d.kind {
                self.g.defs[did.0 as usize].opaque = true;
            }
            sigs.insert(k, sig);
        }
        sigs
    }

    fn phase_bodies(&mut self, m: &ast::Module, ids: &[Option<Sym>], mut sigs: HashMap<usize, Sig>) {
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
                    if let Some(e) = decreasing {
                        self.check_measure(&mut sig.cx, e);
                    }
                    let rty = self.eval(&sig.cx, &sig.result);
                    let bt = self.check_block(&mut sig.cx, body, &rty, true);
                    self.solve_deferred();
                    self.report_unsolved_sig(*did, &sig, d.span);
                    let full = Self::lam_of(&sig.binders, bt);
                    crate::usage::check_fn(self, *did, &full);
                    self.g.defs[did.0 as usize].body = Some(full);
                    self.cur_fn = None;
                }
                DeclKind::Lemma { lets, ensures, .. } => {
                    let Some(mut sig) = sigs.remove(&k) else { continue };
                    let start = sig.cx.lvl();
                    for (p, e) in lets {
                        let (t, ty) = self.infer(&mut sig.cx, e);
                        match &p.kind {
                            ast::PatKind::Var(n) => {
                                let v = self.eval(&sig.cx, &t);
                                sig.cx.define(n, ty, v, Mult::Zero);
                            }
                            _ => {
                                self.err(Diagnostic::error(
                                    "E0357",
                                    "`let` in a lemma header binds a single name",
                                    p.span,
                                ));
                            }
                        }
                    }
                    self.elab_pred(&mut sig.cx, ensures, "lemma");
                    sig.cx.truncate(start);
                    self.solve_deferred();
                }
                DeclKind::Check { expr } => {
                    let mut cx = Cx::default();
                    let b = self.bool_ty();
                    self.check(&mut cx, expr, &b, false);
                    self.solve_deferred();
                    self.obligations.push(Obligation { module: self.cur.clone(), span: expr.span, what: "check" });
                }
                _ => {}
            }
        }
    }

    fn check_measure(&mut self, cx: &mut Cx, e: &Expr) {
        let n = self.nat();
        match &e.kind {
            ExprKind::Tuple(items) => {
                for it in items {
                    self.check(cx, it, &n, false);
                }
            }
            _ => {
                self.check(cx, e, &n, false);
            }
        }
        self.obligations.push(Obligation { module: self.cur.clone(), span: e.span, what: "termination measure" });
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
