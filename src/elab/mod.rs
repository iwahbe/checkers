//! Elaboration: surface AST → core terms, with type checking (M1).
//!
//! Bidirectional checking with implicit arguments solved by pattern
//! unification. `match` is compiled to case trees with exhaustiveness
//! checking (D4). Predicates in constraints are type-checked as `Bool` and
//! recorded for the prover (M3).

mod decls;
mod expr;
mod pattern;
pub mod stdlib;
mod termination;

use crate::core::*;
use crate::diag::Diagnostic;
use crate::source::{SourceFile, Span};
use crate::syntax::ast;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sym {
    Def(DefId),
    Ty(TyId),
    Con(ConId),
    /// Overloaded built-ins (D38)
    Len,
    Format,
    Univ,
}

#[derive(Default)]
pub struct ModuleInfo {
    pub name: String,
    pub types: HashMap<String, Sym>,
    pub values: HashMap<String, Sym>,
    pub exported_types: HashSet<String>,
    pub exported_values: HashSet<String>,
    /// Unqualified names brought in by imports.
    pub import_types: HashMap<String, Sym>,
    pub import_values: HashMap<String, Sym>,
    /// Qualifier (module name or alias) → module name.
    pub qualifiers: HashMap<String, String>,
}

/// Per-function facts used by the termination and usage checks.
#[derive(Clone, Default)]
pub struct FnMeta {
    pub name: String,
    pub span: Span,
    pub partial: bool,
    pub decreasing: bool,
    pub is_fn: bool,
    /// Explicit parameter names and multiplicities, in order.
    pub params: Vec<(String, Mult, Span)>,
    pub n_implicit: usize,
    pub builtin: bool,
}

#[derive(Clone, Debug)]
pub struct CallRec {
    pub caller: DefId,
    pub callee: DefId,
    /// For each explicit argument: Some(p) if it is a strict structural subterm of the caller's parameter p.
    pub args: Vec<Option<usize>>,
    pub span: Span,
}

#[derive(Clone)]
pub struct Local {
    pub name: Name,
    pub ty: Val,
    pub mult: Mult,
    /// λ-bound (as opposed to let-defined); metas abstract over bound locals.
    pub bound: bool,
    /// This local *is* explicit parameter p of the current function.
    pub param: Option<usize>,
    /// This local is a strict structural subterm of parameter p.
    pub sub: Option<usize>,
}

#[derive(Clone, Default)]
pub struct Cx {
    pub env: Vec<Val>,
    pub locals: Vec<Local>,
    /// Elaborating a type position (after `~`): `Uname`s prefer the type namespace (D26).
    pub type_pos: bool,
}

impl Cx {
    pub fn lvl(&self) -> usize {
        self.locals.len()
    }
    pub fn env(&self) -> Env {
        Rc::new(self.env.clone())
    }
    pub fn names(&self) -> Vec<Name> {
        self.locals.iter().map(|l| l.name.clone()).collect()
    }
    pub fn bind(&mut self, name: &str, ty: Val, mult: Mult) -> usize {
        let l = self.lvl();
        self.env.push(Val::var(l));
        self.locals.push(Local { name: Rc::from(name), ty, mult, bound: true, param: None, sub: None });
        l
    }
    pub fn define(&mut self, name: &str, ty: Val, val: Val, mult: Mult) -> usize {
        let l = self.lvl();
        self.env.push(val);
        self.locals.push(Local { name: Rc::from(name), ty, mult, bound: false, param: None, sub: None });
        l
    }
    pub fn pop(&mut self) {
        self.env.pop();
        self.locals.pop();
    }
    pub fn truncate(&mut self, n: usize) {
        self.env.truncate(n);
        self.locals.truncate(n);
    }
    pub fn lookup(&self, name: &str) -> Option<usize> {
        self.locals.iter().rposition(|l| l.name.as_ref() == name)
    }
    pub fn var(&self, lvl: usize) -> Tm {
        Tm::Var(self.lvl() - lvl - 1)
    }
}

/// A constraint on an operator's operand type, checked after the declaration (D38).
#[derive(Clone)]
pub struct Deferred {
    pub ty: Val,
    pub kind: OpClass,
    pub span: Span,
    pub what: String,
    pub lvl: usize,
    pub names: Vec<Name>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum OpClass {
    Numeric,
    Ordered,
    Concat,
    HasLen,
}

/// Predicates recorded for the prover (M3).
#[derive(Clone)]
pub struct Obligation {
    pub module: String,
    pub span: Span,
    pub what: &'static str,
}

pub struct Elab {
    pub g: Globals,
    pub modules: HashMap<String, ModuleInfo>,
    pub sources: HashMap<String, SourceFile>,
    pub diags: Vec<(String, Diagnostic)>,
    seen: HashSet<(String, u32, u32, String)>,
    pub cur: String,
    loading: Vec<String>,
    pub deferred: Vec<Deferred>,
    pub fn_meta: HashMap<DefId, FnMeta>,
    pub cur_fn: Option<DefId>,
    pub calls: Vec<CallRec>,
    /// Definitions whose bodies are being elaborated in this module (termination groups).
    pub module_fns: Vec<DefId>,
    pub obligations: Vec<Obligation>,
    /// `check` declarations: module, span, elaborated `Bool` term (D40).
    pub checks: Vec<(String, Span, Tm)>,
    /// Variables that are linear because of their type (D39): (function, name) → (span, type).
    pub resource_vars: HashMap<(DefId, String), (Span, String)>,
    /// The function result type when elaborating a tail position (for `try`).
    pub stdlib_mode: bool,
    /// Element locals of `map f xs` where xs is a subterm of parameter p.
    pub map_elem_sub: Option<usize>,
    /// Span of the `match` being compiled (for exhaustiveness errors).
    pub match_span: Span,
    /// Exhaustiveness state of the `match` being compiled.
    pub pm: pattern::PatState,
}

pub struct Failed;

impl Elab {
    pub fn new() -> Elab {
        Elab {
            g: Globals::new(),
            modules: HashMap::new(),
            sources: HashMap::new(),
            diags: Vec::new(),
            seen: HashSet::new(),
            cur: String::new(),
            loading: Vec::new(),
            deferred: Vec::new(),
            fn_meta: HashMap::new(),
            cur_fn: None,
            calls: Vec::new(),
            module_fns: Vec::new(),
            obligations: Vec::new(),
            checks: Vec::new(),
            resource_vars: HashMap::new(),
            stdlib_mode: false,
            map_elem_sub: None,
            match_span: Span::default(),
            pm: Default::default(),
        }
    }

    pub fn err(&mut self, d: Diagnostic) {
        // An unknown name is reported at its first use only; the fix is the same for all.
        let (start, end) = if d.code == "E0204" { (0, 0) } else { (d.span.start, d.span.end) };
        let key = (self.cur.clone(), start, end, d.message.clone());
        if self.seen.insert(key) {
            self.diags.push((self.cur.clone(), d));
        }
    }

    pub fn show_val(&self, cx: &Cx, v: &Val) -> String {
        let t = quote(&self.g, cx.lvl(), v);
        show(&self.g, &cx.names(), &t)
    }

    pub fn eval(&self, cx: &Cx, t: &Tm) -> Val {
        eval(&self.g, &cx.env(), t)
    }

    pub fn force(&self, v: &Val) -> Val {
        force(&self.g, v.clone())
    }

    /// A fresh meta applied to the bound locals in scope.
    pub fn fresh_meta(&mut self, cx: &Cx) -> Tm {
        let m = self.g.fresh_meta();
        let mut t = Tm::Meta(m);
        for (lvl, l) in cx.locals.iter().enumerate() {
            if l.bound {
                t = Tm::App(Rc::new(t), Rc::new(cx.var(lvl)), Icit::Expl, Mult::Many);
            }
        }
        t
    }

    pub fn fresh_meta_val(&mut self, cx: &Cx) -> Val {
        let t = self.fresh_meta(cx);
        self.eval(cx, &t)
    }

    /// Unify, reporting a type mismatch on failure. Returns false on failure.
    pub fn unify_at(&mut self, cx: &Cx, expected: &Val, actual: &Val, span: Span, what: &str) -> bool {
        match unify(&self.g, cx.lvl(), expected, actual) {
            Ok(()) => true,
            Err(_) => {
                let e = self.show_val(cx, expected);
                let a = self.show_val(cx, actual);
                self.err(
                    Diagnostic::error("E0201", format!("type mismatch: expected `{e}`, found `{a}`"), span)
                        .with_label(format!("{what} has type `{a}`")),
                );
                false
            }
        }
    }

    /// A primitive resource (D39): implemented by the runtime as an open, stateful thing.
    fn is_primitive_resource(&self, t: TyId) -> bool {
        let ti = &self.g.tys[t.0 as usize];
        &*ti.module == "files" && &*ti.name == "File"
    }

    /// Does this type declaration contain a resource (in a constructor field)?
    /// A cown or future owns its contents; its handle may be shared (D39).
    fn is_owner(&self, t: TyId) -> bool {
        Some(t) == self.g.well_known.cown || Some(t) == self.g.well_known.future
    }

    fn ty_linear(&self, t: TyId, visiting: &mut Vec<TyId>) -> bool {
        if self.is_primitive_resource(t) {
            return true;
        }
        if self.is_owner(t) {
            return false;
        }
        if visiting.contains(&t) {
            return false;
        }
        visiting.push(t);
        let ti = &self.g.tys[t.0 as usize];
        let r = ti
            .ctors
            .iter()
            .any(|c| self.g.cons[c.0 as usize].fields.iter().any(|f| f.1 != Mult::Zero && self.tm_linear(&f.3, visiting)));
        visiting.pop();
        r
    }

    fn tm_linear(&self, t: &Tm, visiting: &mut Vec<TyId>) -> bool {
        match t {
            Tm::TyCon(id) => self.ty_linear(*id, visiting),
            Tm::TyConApp(id, args) => {
                !self.is_owner(*id) && (self.ty_linear(*id, visiting) || args.iter().any(|a| self.tm_linear(a, visiting)))
            }
            Tm::TupleTy(ts) => ts.iter().any(|a| self.tm_linear(a, visiting)),
            Tm::Meta(m) => match self.g.meta(*m) {
                Some(v) => self.val_linear(&v),
                None => false,
            },
            _ => false,
        }
    }

    /// Is a value of this type linear (D39)?
    pub fn val_linear(&self, v: &Val) -> bool {
        match self.force(v) {
            Val::TyCon(id, args) => {
                !self.is_owner(id) && (self.ty_linear(id, &mut Vec::new()) || args.iter().any(|a| self.val_linear(a)))
            }
            Val::TupleTy(ts) => ts.iter().any(|a| self.val_linear(a)),
            _ => false,
        }
    }

    pub fn type_linear(&self, t: &Tm) -> bool {
        self.tm_linear(t, &mut Vec::new())
    }

    /// The multiplicity for a variable the program names: linear types make it `own` (D39).
    pub fn named_mult(&mut self, cx: &Cx, name: &str, ty: &Val, span: Span, declared: Mult) -> Mult {
        if declared != Mult::Many || name == "_" || name.starts_with('$') || !self.val_linear(ty) {
            return declared;
        }
        if let Some(f) = self.cur_fn {
            let shown = self.show_val(cx, ty);
            self.resource_vars.insert((f, name.to_string()), (span, shown));
        }
        Mult::One
    }

    /// D45: `own` belongs on generic parameters. On a linear type it is implied
    /// (W010); on a type without type variables it means nothing useful (E0357).
    pub fn check_own(&mut self, cx: &Cx, ty: &Tm, span: Span) {
        if self.type_linear(ty) {
            let tyv = self.eval(cx, ty);
            let shown = self.show_val(cx, &tyv);
            self.err(
                Diagnostic::warning("W010", format!("`own` is implied: `{shown}` holds a resource"), span)
                    .with_label("this `own` can go")
                    .with_help("remove `own`; a resource is used exactly once anyway"),
            );
        } else if !self.mentions_type_var(cx, ty, 0) {
            let tyv = self.eval(cx, ty);
            let shown = self.show_val(cx, &tyv);
            self.err(
                Diagnostic::error("E0357", format!("`own` on `{shown}`, which holds no resource"), span)
                    .with_label("`own` has no use here")
                    .with_help("`own` is for generic parameters that may receive a resource, as in `v~own a`; remove it"),
            );
        }
    }

    fn mentions_type_var(&self, cx: &Cx, t: &Tm, under: usize) -> bool {
        match t {
            Tm::Var(i) if *i >= under => {
                let lvl = cx.lvl() + under - 1 - i;
                lvl < cx.locals.len() && matches!(self.force(&cx.locals[lvl].ty), Val::Univ(_))
            }
            Tm::App(f, a, ..) => self.mentions_type_var(cx, f, under) || self.mentions_type_var(cx, a, under),
            Tm::TyConApp(_, v) | Tm::TupleTy(v) => v.iter().any(|a| self.mentions_type_var(cx, a, under)),
            Tm::Pi(_, _, _, a, b) => self.mentions_type_var(cx, a, under) || self.mentions_type_var(cx, b, under + 1),
            Tm::Meta(m) => self.g.meta(*m).is_none(),
            _ => false,
        }
    }

    /// E0404: a pattern or `_` that would drop a resource.
    pub fn report_dropped(&mut self, cx: &Cx, ty: &Val, span: Span) {
        let shown = self.show_val(cx, ty);
        self.err(
            Diagnostic::error("E0404", format!("this drops a resource of type `{shown}`"), span)
                .with_label("a resource must be used exactly once")
                .with_help("bind it to a name, then close it or pass it on"),
        );
    }

    pub fn is_ty(&self, v: &Val, t: Option<TyId>) -> bool {
        matches!((self.force(v), t), (Val::TyCon(a, _), Some(b)) if a == b)
    }

    pub fn ty_val(&self, t: Option<TyId>, args: Vec<Val>) -> Val {
        match t {
            Some(t) => Val::TyCon(t, args),
            None => Val::Error,
        }
    }

    pub fn nat(&self) -> Val {
        self.ty_val(self.g.well_known.nat, vec![])
    }
    pub fn int(&self) -> Val {
        self.ty_val(self.g.well_known.int, vec![])
    }
    pub fn bool_ty(&self) -> Val {
        self.ty_val(self.g.well_known.bool_ty, vec![])
    }
    pub fn string(&self) -> Val {
        self.ty_val(self.g.well_known.string, vec![])
    }
    pub fn bytes(&self) -> Val {
        self.ty_val(self.g.well_known.bytes, vec![])
    }
    pub fn unit(&self) -> Val {
        Val::TupleTy(vec![])
    }

    pub fn module(&self) -> &ModuleInfo {
        &self.modules[&self.cur]
    }

    /// Check deferred operator constraints and default unconstrained numerals to `Nat`.
    /// If `ty` is an unsolved type that an operator or literal requires to be a
    /// number, default it to `Nat` now and return true. Such a type can never
    /// be a function or `Unit`, so this only sharpens error messages.
    pub fn default_if_numeric(&mut self, ty: &Val) -> bool {
        let Val::Neutral(Head::Meta(m), _) = self.force(ty) else { return false };
        let hit = self.deferred.iter().find_map(|d| {
            if !matches!(d.kind, OpClass::Numeric | OpClass::Ordered) {
                return None;
            }
            match self.force(&d.ty) {
                Val::Neutral(Head::Meta(m2), _) if m2 == m => Some((d.ty.clone(), d.lvl)),
                _ => None,
            }
        });
        match hit {
            Some((dty, lvl)) => {
                let n = self.nat();
                unify(&self.g, lvl, &dty, &n).is_ok()
            }
            None => false,
        }
    }

    pub fn solve_deferred(&mut self) {
        let ds = std::mem::take(&mut self.deferred);
        for d in &ds {
            if let Val::Neutral(Head::Meta(_), _) = self.force(&d.ty) {
                if matches!(d.kind, OpClass::Numeric | OpClass::Ordered) {
                    let n = self.nat();
                    let _ = unify(&self.g, d.lvl, &d.ty, &n);
                }
            }
        }
        for d in ds {
            let t = self.force(&d.ty);
            let wk = &self.g.well_known;
            let ok = match (&t, d.kind) {
                (Val::Error, _) => true,
                (Val::Neutral(Head::Meta(_), _), _) => true,
                (Val::TyCon(id, _), OpClass::Numeric | OpClass::Ordered) => {
                    Some(*id) == wk.nat || Some(*id) == wk.int
                }
                (Val::TyCon(id, _), OpClass::Concat | OpClass::HasLen) => {
                    Some(*id) == wk.string || Some(*id) == wk.bytes || Some(*id) == wk.list
                }
                _ => false,
            };
            if !ok {
                let shown = show(&self.g, &d.names, &quote(&self.g, d.lvl, &t));
                let need = match d.kind {
                    OpClass::Numeric => "numbers (`Nat` or `Int`)",
                    OpClass::Ordered => "numbers (`Nat` or `Int`) to compare",
                    OpClass::Concat => "a `String`, `Bytes` or `List`",
                    OpClass::HasLen => "a `String`, `Bytes` or `List`",
                };
                let mut diag = Diagnostic::error("E0210", format!("{} needs {need}, but this is `{shown}`", d.what), d.span)
                    .with_label(format!("has type `{shown}`"));
                if d.what == "`+`" && matches!(&t, Val::TyCon(id, _) if Some(*id) == wk.string || Some(*id) == wk.bytes || Some(*id) == wk.list) {
                    diag = diag.with_help("to join strings, bytes or lists, use `++`");
                }
                self.err(diag);
            }
        }
    }

    pub fn number(&mut self, s: &str, span: Span) -> i128 {
        let r = if let Some(h) = s.strip_prefix("0x") { i128::from_str_radix(h, 16) } else { s.parse::<i128>() };
        match r {
            Ok(n) => n,
            Err(_) => {
                self.err(Diagnostic::error(
                    "E0211",
                    "number literal is too large (the type checker currently supports 127-bit literals)",
                    span,
                ));
                0
            }
        }
    }
}

impl Default for Elab {
    fn default() -> Self {
        Self::new()
    }
}

/// Elaborate a user module (and the standard library modules it needs).
pub fn check_module(name_hint: &str, file: &SourceFile, m: &ast::Module) -> Elab {
    let mut e = Elab::new();
    // Core stdlib modules are always loaded: they define well-known types.
    for core in ["prelude", "cown", "future", "system"] {
        e.load_stdlib(core);
    }
    let name = m.name.as_ref().map(|q| q.dotted()).unwrap_or_else(|| name_hint.to_string());
    e.sources.insert(name.clone(), SourceFile::new(file.name.clone(), file.text.clone()));
    e.elab_module(&name, m, false);
    e
}
