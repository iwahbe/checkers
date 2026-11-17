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
    /// `Type`, declared in the prelude (D132).
    Univ,
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
    Local { name: String, def: Option<(String, Span)>, ty: String, param: bool, ty_head: Option<TyId> },
    /// A module name (`import a.b`, `b.f`).
    Module(String),
}

impl Elab {
    /// Names are indexed in the module being checked only (the editor's
    /// document); other modules' declarations still record where they are
    /// and their headers, for hover and go to definition.
    pub fn indexing(&self) -> bool {
        self.index_of.as_deref() == Some(self.cur.as_str()) || self.index_all.as_ref().is_some_and(|m| m.contains(&self.cur))
    }

    pub fn index_global(&mut self, span: Span, t: Target) {
        let kind = match t {
            Target::Con(_) => super::unused::RefKind::Build,
            Target::Field(..) => super::unused::RefKind::Read,
            _ => super::unused::RefKind::Use,
        };
        self.reference(span, t, kind);
        self.index_name(span, t);
    }

    /// A constructor matched in a pattern: used, but not built (D144).
    pub fn index_pattern(&mut self, span: Span, t: Target) {
        self.reference(span, t, super::unused::RefKind::Match);
        self.index_name(span, t);
    }

    /// A name in an import's list: an occurrence of what it imports, for
    /// references and rename (D161), not a use (D144).
    pub fn index_import(&mut self, span: Span, s: Sym) {
        match s {
            Sym::Def(d) => self.index_name(span, Target::Def(d)),
            Sym::Ty(t) => self.index_name(span, Target::Ty(t)),
            Sym::Con(c) => self.index_name(span, Target::Con(c)),
            _ => {}
        }
    }

    fn index_name(&mut self, span: Span, t: Target) {
        // Code shown from another module (D136) isn't in this file.
        if self.indexing() && span.start < super::SYNTHETIC {
            self.index.push(NameUse { module: self.cur.clone(), span, what: Use::Global(t) });
        }
    }

    pub fn index_sym(&mut self, span: Span, s: Sym) {
        match s {
            Sym::Def(d) => self.index_global(span, Target::Def(d)),
            Sym::Ty(t) => self.index_global(span, Target::Ty(t)),
            Sym::Con(c) => self.index_global(span, Target::Con(c)),
            Sym::Univ => self.index_global(span, Target::Univ),
            _ => {}
        }
    }

    /// A declaration of `t` at `span`: where go to definition lands, and an
    /// occurrence of its name.
    pub fn index_decl(&mut self, span: Span, t: Target) {
        self.decl_at.insert(t, (self.cur.clone(), span));
        self.index_name(span, t);
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
        let ty_head = match self.force(&local.ty) {
            Val::TyCon(t, _) => Some(t),
            _ => None,
        };
        let def = local.span.map(|s| (self.cur.clone(), s));
        if span.start >= super::SYNTHETIC {
            return;
        }
        self.index.push(NameUse {
            module: self.cur.clone(),
            span,
            what: Use::Local { name: local.name.to_string(), def, ty, param: local.param.is_some(), ty_head },
        });
    }

    /// Bind-site bookkeeping: the local at `l` was bound by the name at `span`.
    pub fn bound_at(&mut self, cx: &mut Cx, l: usize, span: Span) {
        cx.locals[l].span = Some(span);
        // For usage messages about a local that holds no resource (D171).
        if let Some(f) = self.cur_fn {
            self.local_spans.entry((f, cx.locals[l].name.to_string())).or_insert(span);
        }
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
            Use::Global(Target::Ty(_) | Target::Univ) => "type",
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
                    Target::Univ => "Type".to_string(),
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

    /// Where go to type definition goes (D160): the declaration of the
    /// type of a local, a constant, a field or a constructor's value, or of
    /// a function's result.
    pub fn type_def_of(&self, u: &Use) -> Option<(String, Span)> {
        fn head(t: &Tm) -> Option<TyId> {
            match t {
                Tm::Pi(_, _, _, _, b) => head(b),
                Tm::TyCon(t) | Tm::TyConApp(t, _) => Some(*t),
                _ => None,
            }
        }
        let t = match u {
            Use::Local { ty_head, .. } => (*ty_head)?,
            Use::Global(Target::Ty(t)) => *t,
            Use::Global(Target::Def(d)) => head(&self.g.defs[d.0 as usize].ty)?,
            Use::Global(Target::Con(c)) => self.g.cons[c.0 as usize].ty,
            Use::Global(Target::Field(c, k)) => head(&self.g.cons[c.0 as usize].fields[*k].3)?,
            Use::Global(Target::Univ) | Use::Module(_) => return None,
        };
        self.decl_at.get(&Target::Ty(t)).cloned()
    }

    /// Whether every use of the name is in the modules indexed (`user`):
    /// a local, or a declaration of one of them; one it exports only when
    /// every module of its package is indexed (D160, D161). Renaming it
    /// there renames it everywhere.
    pub fn renamable(&self, u: &Use, user: &dyn Fn(&str) -> bool) -> bool {
        let (m, name, is_type) = match u {
            Use::Local { .. } => return true,
            Use::Module(_) | Use::Global(Target::Univ) => return false,
            Use::Global(t) => {
                let Some((m, _)) = self.decl_at.get(t) else { return false };
                match t {
                    Target::Def(d) => (m, self.g.defs[d.0 as usize].name.to_string(), false),
                    Target::Ty(t) => (m, self.g.tys[t.0 as usize].name.to_string(), true),
                    // Constructors and fields are seen wherever their type is.
                    Target::Con(c) | Target::Field(c, _) => {
                        let ty = self.g.cons[c.0 as usize].ty;
                        (m, self.g.tys[ty.0 as usize].name.to_string(), true)
                    }
                    Target::Univ => return false,
                }
            }
        };
        if !user(m) || m.starts_with("std.") {
            return false;
        }
        if self.index_all.is_some() {
            return true;
        }
        match self.modules.get(m) {
            Some(info) => !(if is_type { info.exported_types.contains(&name) } else { info.exported_values.contains(&name) }),
            None => false,
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
