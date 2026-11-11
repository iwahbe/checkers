//! The index of names (§15.5, D120): each name in the program's own modules,
//! what it refers to, its kind and its type, for hover, go to definition and
//! highlighting in the language server. Recorded while elaborating; the
//! standard library's modules are not indexed.

use super::*;

/// What a name refers to.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Target {
    Def(DefId),
    Ty(TyId),
    Con(ConId),
    /// Field `k` of a constructor (a record's fields, an enum constructor's).
    Field(ConId, usize),
}

/// One occurrence of a name.
#[derive(Clone, Debug)]
pub struct NameUse {
    pub module: String,
    pub span: Span,
    pub what: Use,
}

#[derive(Clone, Debug)]
pub enum Use {
    Global(Target),
    /// A local: its binding (if known), its type as shown, and whether it is
    /// a parameter.
    Local { name: String, def: Option<(String, Span)>, ty: String, param: bool },
    /// A module name (`import a.b`, `b.f`).
    Module(String),
}

impl Elab {
    /// Names are indexed in the module being checked only (the editor's
    /// document); other modules' declarations still record where they are
    /// and their headers, for hover and go to definition.
    pub fn indexing(&self) -> bool {
        self.index_of.as_deref() == Some(self.cur.as_str())
    }

    pub fn index_global(&mut self, span: Span, t: Target) {
        if self.indexing() {
            self.index.push(NameUse { module: self.cur.clone(), span, what: Use::Global(t) });
        }
    }

    pub fn index_sym(&mut self, span: Span, s: Sym) {
        match s {
            Sym::Def(d) => self.index_global(span, Target::Def(d)),
            Sym::Ty(t) => self.index_global(span, Target::Ty(t)),
            Sym::Con(c) => self.index_global(span, Target::Con(c)),
            _ => {}
        }
    }

    /// A declaration of `t` at `span`: where go to definition lands, and an
    /// occurrence of its name.
    pub fn index_decl(&mut self, span: Span, t: Target) {
        self.decl_at.insert(t, (self.cur.clone(), span));
        self.index_global(span, t);
    }

    /// The local at level `l` used (or bound) at `span`.
    pub fn index_local(&mut self, cx: &Cx, l: usize, span: Span) {
        if !self.indexing() {
            return;
        }
        let local = &cx.locals[l];
        if local.name.starts_with('$') || local.name.as_ref() == "_" {
            return;
        }
        let ty = self.show_val(cx, &local.ty);
        let def = local.span.map(|s| (self.cur.clone(), s));
        self.index.push(NameUse {
            module: self.cur.clone(),
            span,
            what: Use::Local { name: local.name.to_string(), def, ty, param: local.param.is_some() },
        });
    }

    /// Bind-site bookkeeping: the local at `l` was bound by the name at `span`.
    pub fn bound_at(&mut self, cx: &mut Cx, l: usize, span: Span) {
        cx.locals[l].span = Some(span);
        self.index_local(cx, l, span);
    }

    pub fn index_module(&mut self, span: Span, module: &str) {
        if self.indexing() {
            self.index.push(NameUse { module: self.cur.clone(), span, what: Use::Module(module.to_string()) });
        }
    }

    /// The kind of a name, as the language server's semantic tokens name it.
    pub fn class_of(&self, u: &Use) -> &'static str {
        match u {
            Use::Global(Target::Def(d)) => self.def_class.get(d).copied().unwrap_or("function"),
            Use::Global(Target::Ty(_)) => "type",
            Use::Global(Target::Con(_)) => "constructor",
            Use::Global(Target::Field(..)) => "field",
            Use::Local { param: true, .. } => "parameter",
            Use::Local { .. } => "variable",
            Use::Module(_) => "module",
        }
    }

    /// What hovering over the name shows.
    pub fn hover_of(&self, u: &Use) -> String {
        match u {
            Use::Global(t) => {
                if let Some(sig) = self.decl_sig.get(t) {
                    return sig.clone();
                }
                match t {
                    Target::Def(d) => {
                        let info = &self.g.defs[d.0 as usize];
                        format!("{} : {}", info.name, crate::core::show(&self.g, &[], &info.ty))
                    }
                    Target::Ty(t) => format!("type {}", self.g.tys[t.0 as usize].name),
                    Target::Con(c) => {
                        let ty = self.con_type(*c);
                        format!("{} : {}", self.g.cons[c.0 as usize].name, crate::core::show(&self.g, &[], &ty))
                    }
                    Target::Field(c, k) => {
                        let ci = &self.g.cons[c.0 as usize];
                        let (n, _, _, _) = &ci.fields[*k];
                        format!("{} (field of `{}`)", n, ci.name)
                    }
                }
            }
            Use::Local { name, ty, .. } => format!("{name} : {ty}"),
            Use::Module(m) => format!("module {m}"),
        }
    }

    /// Where go to definition goes: (module, span).
    pub fn def_of(&self, u: &Use) -> Option<(String, Span)> {
        match u {
            Use::Global(t) => self.decl_at.get(t).cloned(),
            Use::Local { def, .. } => def.clone(),
            Use::Module(m) => Some((m.clone(), Span::new(0, 0))),
        }
    }
}
