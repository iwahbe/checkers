//! Elaboration: surface AST → core terms, with type checking (M1).
//!
//! Bidirectional checking with implicit arguments solved by pattern
//! unification. `match` is compiled to case trees with exhaustiveness
//! checking (D4). Predicates in constraints are type-checked as `Bool` and
//! recorded for the prover (M3).

mod decls;
mod expr;
mod order;
mod pattern;
mod refine;
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
    /// Qualifiers of imports that failed: their uses are already reported.
    pub failed_imports: HashSet<String>,
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
    /// The result's name, if it has one (`-> y`).
    pub result: Option<String>,
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
    /// Known at compile time (§8.9): a `comptime` parameter, or a field of one.
    pub comptime: bool,
}

#[derive(Clone, Default)]
pub struct Cx {
    pub env: Vec<Val>,
    pub locals: Vec<Local>,
    /// Elaborating a type position (after `~`): `Uname`s prefer the type namespace (D26).
    pub type_pos: bool,
    /// Facts in scope (§7.1): `Bool` values known to be true, tagged with the
    /// context length when they were added.
    pub facts: Vec<(usize, Val)>,
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
        self.locals.push(Local { name: Rc::from(name), ty, mult, bound: true, param: None, sub: None, comptime: false });
        l
    }
    pub fn define(&mut self, name: &str, ty: Val, val: Val, mult: Mult) -> usize {
        let l = self.lvl();
        self.env.push(val);
        self.locals.push(Local { name: Rc::from(name), ty, mult, bound: false, param: None, sub: None, comptime: false });
        l
    }
    pub fn pop(&mut self) {
        self.env.pop();
        self.locals.pop();
        let n = self.locals.len();
        self.facts.retain(|(l, _)| *l <= n);
    }
    pub fn truncate(&mut self, n: usize) {
        self.env.truncate(n);
        self.locals.truncate(n);
        self.facts.retain(|(l, _)| *l <= n);
    }
    pub fn assume(&mut self, fact: Val) {
        self.facts.push((self.locals.len(), fact));
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
/// What an obligation is for; decides how a failure is reported (§7.1).
#[derive(Clone, Debug)]
pub enum ObKind {
    Pre { callee: String },
    Post { func: String, at: Span },
    Invariant { con: String },
    /// A behaviour must hand back contents of the cown's refinement (§8.5).
    CownInvariant { alias: String },
    /// A value checked against a refinement alias from a type argument (D71).
    Refined { alias: String, value: String },
    /// A refinement replaced by another in a type (D83, D85): for any value
    /// of `sub`, the predicates of `sup` hold.
    Weaken { role: WeakenRole, value: String, sub: String, sup: String, callee: Option<String> },
    NatSub,
    /// A recursive call must make the caller's `decreasing` measure smaller.
    Measure { func: String, measure: String },
    Div,
    Index,
    Lemma { name: String },
    Auto,
    Have,
}

/// Where a refinement is weakened (D83, D85).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WeakenRole {
    /// The values a type holds (`List (n~Int, n >= 6)` as `List Big`).
    Element,
    /// A function's parameter: the function is given more than it accepts.
    Param,
    /// A function's result: it may return less than is promised.
    Result,
}

/// A local in an obligation's context.
#[derive(Clone)]
pub struct ObLocal {
    pub name: Name,
    pub ty: Val,
    /// The value of a `let`-bound local.
    pub def: Option<Val>,
}

/// `Γ ⊢ goal` (§7.1). Values are level-based over `ctx`.
#[derive(Clone)]
pub struct Obligation {
    pub module: String,
    pub span: Span,
    pub kind: ObKind,
    /// The predicate as written, for messages.
    pub text: String,
    pub ctx: Vec<ObLocal>,
    pub facts: Vec<Val>,
    pub goal: Val,
    /// Only an obligation if this type turns out to be `Nat` (subtraction).
    pub only_if_nat: Option<Val>,
    pub owner: Option<DefId>,
}

/// A predicate from a header, constructor or alias, as a term over its binders.
#[derive(Clone)]
pub struct Pred {
    pub tm: Tm,
    pub text: String,
    pub span: Span,
    pub is_post: bool,
    /// From a refinement-alias type on binder `k` (`c~Char`), not a written predicate.
    pub alias: Option<(usize, DefId)>,
}

/// The specification of a function or lemma. Predicates are terms over the
/// binders (implicit then explicit) followed by the result.
#[derive(Clone, Default)]
pub struct Spec {
    pub preds: Vec<Pred>,
    pub n_binders: usize,
    pub n_implicit: usize,
    /// A lemma's `let`s (each over the binders and earlier lets) and its `ensures`.
    pub lets: Vec<Tm>,
    pub ensures: Option<Pred>,
    /// `decreasing e` / `decreasing (a, b)`: components over the binders, and the text.
    pub measure: Option<(Vec<Tm>, String)>,
}

/// The postconditions to check at each value the current function returns.
#[derive(Clone)]
pub struct PostTarget {
    pub posts: Vec<Pred>,
    pub func: String,
    /// The values of the function's binders (its parameters).
    pub binders: Vec<Val>,
    /// In a `when` body: the refinements the new contents must satisfy (§8.5).
    pub invariants: Vec<CownInv>,
}

/// A cown's content refinement (`type Log = …, len entries <= 100`), to be
/// re-established by a behaviour.
#[derive(Clone)]
pub struct CownInv {
    pub alias: String,
    /// The alias's predicates over `args ++ [subject]`.
    pub preds: Vec<Pred>,
    pub args: Vec<Val>,
    /// The component of the body's tuple, with several cowns.
    pub proj: Option<usize>,
}

/// A trust-ledger entry (§7.4) for something accepted without a solver proof.
#[derive(Clone, Debug)]
pub struct Trusted {
    pub module: String,
    pub span: Span,
    pub what: String,
}

pub struct Elab {
    pub g: Globals,
    pub modules: HashMap<String, ModuleInfo>,
    pub sources: HashMap<String, SourceFile>,
    pub diags: Vec<(String, Diagnostic)>,
    seen: HashSet<(String, u32, u32, String)>,
    pub cur: String,
    loading: Vec<String>,
    /// Where `import a.b` looks for `a/b.ck` (D53).
    pub base_dir: Option<std::path::PathBuf>,
    /// Imported program modules (not the standard library), dependencies first.
    pub user_modules: Vec<String>,
    /// The package of each module of a dependency (D111); others are the
    /// program's own package, or `std`.
    pub module_pkg: HashMap<String, String>,
    pub deferred: Vec<Deferred>,
    pub fn_meta: HashMap<DefId, FnMeta>,
    pub cur_fn: Option<DefId>,
    pub calls: Vec<CallRec>,
    /// Definitions whose bodies are being elaborated in this module (termination groups).
    pub module_fns: Vec<DefId>,
    pub obligations: Vec<Obligation>,
    pub specs: HashMap<DefId, Spec>,
    /// Functions exported `transparent`: reflected into importers' queries (D12).
    pub transparent: HashSet<DefId>,
    /// Constructor invariants, over the type's parameters then the fields.
    pub con_invs: HashMap<ConId, Vec<Pred>>,
    /// Refinement aliases' predicates, over the alias's parameters then its binder.
    pub alias_preds: HashMap<DefId, Vec<Pred>>,
    /// The name a refinement alias binds (`n` in `type Big = n~Int, …`).
    pub alias_subject: HashMap<DefId, Name>,
    /// The result type of a function whose result type isn't written.
    pub result_metas: HashMap<MetaId, DefId>,
    /// The function whose argument is being checked, for messages (D85).
    pub arg_of: Option<String>,
    /// Inside a type or specification: no obligations (§7.1).
    pub in_spec: usize,
    /// Elaborating the head of an application: a bare function name gets its
    /// refined type only as a value (D85).
    pub in_app_head: bool,
    /// Postconditions to check where the current function returns (§7.1).
    pub post_target: Option<PostTarget>,
    /// The goal of the proof being elaborated (D49).
    pub proof_goal: Option<(Val, String)>,
    pub admits: Vec<Trusted>,
    /// An application checked against a type with a refinement inside: its
    /// result type is unified with this before its arguments are checked (D71).
    pub app_expected: Option<Val>,
    /// The argument being checked is for a parameter or field declared with a
    /// refinement alias, so the call's own obligations cover it (D71).
    pub alias_covered: bool,
    /// The head of the application being elaborated checks its arguments'
    /// refinement aliases (a function with a spec or a constructor with invariants).
    pub head_checks_aliases: bool,
    /// The type an expression checked by inference was found to have.
    pub last_inferred: Option<Val>,
    /// Uses of standard-library lemmas about `__builtin` functions, which are
    /// trusted like the primitives themselves (D56).
    pub builtin_axioms: Vec<Trusted>,
    /// Lemmas whose proof is `__builtin` (D56).
    pub axiom_defs: HashSet<DefId>,
    /// Measure obligations of calls (caller, callee); kept only for calls
    /// inside one recursive group once termination is analysed.
    pub measure_obs: Vec<(DefId, DefId, Obligation)>,
    /// Heads of saturated calls (recursion through a partial application
    /// can't have its measure checked, E0303).
    pub saturated_heads: HashSet<Span>,
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
            base_dir: None,
            user_modules: Vec::new(),
            module_pkg: HashMap::new(),
            deferred: Vec::new(),
            fn_meta: HashMap::new(),
            cur_fn: None,
            calls: Vec::new(),
            module_fns: Vec::new(),
            obligations: Vec::new(),
            checks: Vec::new(),
            specs: HashMap::new(),
            transparent: HashSet::new(),
            con_invs: HashMap::new(),
            alias_preds: HashMap::new(),
            alias_subject: HashMap::new(),
            result_metas: HashMap::new(),
            arg_of: None,
            in_spec: 0,
            in_app_head: false,
            proof_goal: None,
            post_target: None,
            admits: Vec::new(),
            app_expected: None,
            alias_covered: false,
            head_checks_aliases: false,
            last_inferred: None,
            builtin_axioms: Vec::new(),
            axiom_defs: HashSet::new(),
            measure_obs: Vec::new(),
            saturated_heads: HashSet::new(),
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
                // Show computed types (`BadPlaceholder`, not the call that gives it).
                let (expected, actual) = (&self.force(expected), &self.force(actual));
                let e = self.show_val(cx, expected);
                let a = self.show_val(cx, actual);
                // A function checked later whose result type isn't written.
                let pending = [expected, actual].into_iter().find_map(|v| match v {
                    Val::Neutral(Head::Meta(m), _) => self.result_metas.get(m).copied(),
                    _ => None,
                });
                if let Some(f) = pending {
                    let name = self.g.defs[f.0 as usize].name.to_string();
                    self.err(
                        Diagnostic::error("E0201", format!("the result type of `{name}` isn't known yet here"), span)
                            .with_label(format!("`{name}` is checked after this, since they call each other"))
                            .with_help(format!("write `{name}`'s result type in its signature (`-> r : …, r~{e}`)")),
                    );
                    return false;
                }
                let mut d = Diagnostic::error("E0201", format!("type mismatch: expected `{e}`, found `{a}`"), span)
                    .with_label(format!("{what} has type `{a}`"));
                // A sealed function in a type never unfolds outside its module (D54).
                let mut sealed = Vec::new();
                for v in [expected, actual] {
                    collect_sealed(&quote(&self.g, cx.lvl(), v), &self.g, &self.cur, &mut sealed);
                }
                if let Some(dd) = sealed.first() {
                    let info = &self.g.defs[dd.0 as usize];
                    d = d.with_help(format!(
                        "`{}` is defined in `{}`, where function bodies are sealed: its value isn't visible here unless it is exported `transparent`",
                        info.name, info.module
                    ));
                }
                self.err(d);
                false
            }
        }
    }

    /// A primitive resource (D39): implemented by the runtime as an open, stateful thing.
    fn is_primitive_resource(&self, t: TyId) -> bool {
        let ti = &self.g.tys[t.0 as usize];
        &*ti.module == "std.files" && &*ti.name == "File"
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
    /// (W010); on a type without type variables it means nothing useful (E0358).
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
                Diagnostic::error("E0358", format!("`own` on `{shown}`, which holds no resource"), span)
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

    // ── obligations (§7.1) ──────────────────────────────────────────────────

    /// Record `facts in cx ⊢ goal`.
    pub fn oblige(&mut self, cx: &Cx, span: Span, kind: ObKind, text: String, goal: Val, only_if_nat: Option<Val>) {
        if self.in_spec > 0 {
            return;
        }
        let ctx = (0..cx.lvl())
            .map(|l| ObLocal {
                name: cx.locals[l].name.clone(),
                ty: cx.locals[l].ty.clone(),
                def: if cx.locals[l].bound { None } else { Some(cx.env[l].clone()) },
            })
            .collect();
        let facts = cx.facts.iter().map(|(_, v)| v.clone()).collect();
        self.obligations.push(Obligation {
            module: self.cur.clone(),
            span,
            kind,
            text,
            ctx,
            facts,
            goal,
            only_if_nat,
            owner: self.cur_fn,
        });
    }

    /// The postconditions hold of `v`, a value the function returns at `at`.
    pub fn oblige_posts_at(&mut self, cx: &Cx, v: Val, at: Span) {
        let Some(pt) = self.post_target.clone() else { return };
        let mut env = pt.binders.clone();
        env.push(v);
        for p in &pt.posts {
            let goal = self.inst_pred(p, env.clone());
            self.oblige(cx, p.span, ObKind::Post { func: pt.func.clone(), at }, p.text.clone(), goal, None);
        }
        let v = env.pop().unwrap_or(Val::Error);
        for inv in &pt.invariants {
            let subject = match (inv.proj, &v) {
                (None, _) => v.clone(),
                (Some(k), Val::Tuple(xs)) => xs.get(k).cloned().unwrap_or(Val::Error),
                (Some(k), _) => eval(&self.g, &Rc::new(vec![v.clone()]), &Tm::Proj(Rc::new(Tm::Var(0)), k)),
            };
            let mut env = inv.args.clone();
            env.push(subject);
            for p in &inv.preds {
                let goal = self.inst_pred(p, env.clone());
                self.oblige(cx, at, ObKind::CownInvariant { alias: inv.alias.clone() }, p.text.clone(), goal, None);
            }
        }
    }

    /// A cown's content type as a refinement alias: its name, predicates and
    /// argument values (none if the type isn't an alias).
    pub fn cown_inv(&self, cx: &Cx, content: &Val, proj: Option<usize>) -> Option<CownInv> {
        let ty = quote(&self.g, cx.lvl(), content);
        let mut args = Vec::new();
        let mut h = &ty;
        while let Tm::App(f, a, _, _) = h {
            args.push(a.clone());
            h = f;
        }
        let Tm::Def(d) = h else { return None };
        let preds = self.alias_preds.get(d)?.clone();
        args.reverse();
        let env = cx.env();
        let args = args.iter().map(|a| eval(&self.g, &env, a)).collect();
        Some(CownInv { alias: self.g.defs[d.0 as usize].name.to_string(), preds, args, proj })
    }

    pub fn prim_val(p: Prim, args: Vec<Val>) -> Val {
        Val::Neutral(Head::Prim(p, args), Rc::new(Vec::new()))
    }

    pub fn bool_val(&self, b: bool) -> Val {
        let c = if b { self.g.well_known.true_con } else { self.g.well_known.false_con };
        match c {
            Some(c) => Val::Con(c, Vec::new()),
            None => Val::Error,
        }
    }

    /// The fact `v == b` for a `Bool` value `v`.
    pub fn is_bool(&self, v: Val, b: bool) -> Val {
        Self::prim_val(Prim::Eq, vec![v, self.bool_val(b)])
    }

    /// The source text of a span in the current module.
    pub fn src_text(&self, span: Span) -> String {
        self.sources
            .get(&self.cur)
            .and_then(|f| f.text.get(span.start as usize..span.end as usize))
            .map(|t| t.split_whitespace().collect::<Vec<_>>().join(" "))
            .unwrap_or_default()
    }

    /// If `ty`, a type term over the first `at` locals of `cx`, is a refinement
    /// alias (`U8`), its predicates about `subject` (D6, §7.1).
    pub fn alias_facts(&self, cx: &Cx, at: usize, ty: &Tm, subject: Val) -> Vec<(Val, String, DefId)> {
        let mut args = Vec::new();
        let mut h = ty;
        while let Tm::App(f, a, _, _) = h {
            args.push(a.clone());
            h = f;
        }
        let Tm::Def(d) = h else { return Vec::new() };
        let Some(preds) = self.alias_preds.get(d) else { return Vec::new() };
        args.reverse();
        let prefix = Rc::new(cx.env[..at].to_vec());
        let mut env: Vec<Val> = args.iter().map(|a| eval(&self.g, &prefix, a)).collect();
        env.push(subject);
        preds.iter().map(|p| (self.inst_pred(p, env.clone()), p.text.clone(), *d)).collect()
    }

    /// Instantiate a predicate over `binders ++ [result]` with values.
    pub fn inst_pred(&self, p: &Pred, env: Vec<Val>) -> Val {
        eval(&self.g, &Rc::new(env), &p.tm)
    }

    /// Is local `l` known at compile time (§8.9)? A `comptime` parameter or
    /// a field of one, or a `let` whose value is.
    pub fn local_static(&self, cx: &Cx, l: usize) -> bool {
        let loc = &cx.locals[l];
        if loc.comptime {
            return true;
        }
        if loc.bound {
            return false;
        }
        let t = quote(&self.g, l, &cx.env[l]);
        self.tm_static(cx, &t, 0, l)
    }

    /// Does `t` (over the first `at` locals of `cx`, under `depth` more
    /// binders) use only compile-time values, with no effects or `partial`
    /// calls, so that staging can compute it?
    pub fn tm_static(&self, cx: &Cx, t: &Tm, depth: usize, at: usize) -> bool {
        let go = |x: &Tm, d: usize| self.tm_static(cx, x, d, at);
        match t {
            Tm::Var(i) if *i < depth => true,
            Tm::Var(i) => match (at + depth).checked_sub(i + 1) {
                Some(l) if l < at => self.local_static(cx, l),
                _ => false,
            },
            Tm::Def(d) => {
                let info = &self.g.defs[d.0 as usize];
                !(info.opaque && info.body.is_some())
            }
            Tm::PrimApp(Prim::When | Prim::Fork | Prim::Join, _) => false,
            Tm::Pi(_, _, _, a, b) => go(a, depth) && go(b, depth + 1),
            Tm::Lam(_, _, _, b) => go(b, depth + 1),
            Tm::App(f, a, _, m) => go(f, depth) && (*m == Mult::Zero || go(a, depth)),
            Tm::Let(_, _, _, v, b) => go(v, depth) && go(b, depth + 1),
            Tm::TyConApp(_, v) | Tm::TupleTy(v) => v.iter().all(|x| go(x, depth)),
            Tm::ConApp(_, v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => v.iter().all(|x| go(x, depth)),
            Tm::Proj(x, _) | Tm::Field(x, _, _) => go(x, depth),
            Tm::Case(s, c) => {
                go(s, depth)
                    && c.branches.iter().all(|(_, n, b)| go(b, depth + n))
                    && c.lits.iter().all(|(_, b)| go(b, depth))
                    && c.default.as_ref().is_none_or(|b| go(b, depth))
            }
            Tm::Error => false,
            _ => true,
        }
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
pub fn check_module(name_hint: &str, file: &SourceFile, m: &ast::Module, dir: Option<&std::path::Path>) -> Elab {
    let mut e = Elab::new();
    e.base_dir = dir.map(|d| d.to_path_buf());
    // Core stdlib modules are always loaded: they define well-known types.
    for core in ["std.prelude", "std.cown", "std.future", "std.system"] {
        e.load_stdlib(core);
    }
    let name = m.name.as_ref().map(|q| q.dotted()).unwrap_or_else(|| name_hint.to_string());
    e.sources.insert(name.clone(), SourceFile::new(file.name.clone(), file.text.clone()));
    e.elab_module(&name, m, false);
    e
}

/// Definitions sealed by another module (D54) that occur in `t`.
pub fn collect_sealed(t: &Tm, g: &Globals, cur: &str, out: &mut Vec<DefId>) {
    match t {
        Tm::Def(d) => {
            let info = &g.defs[d.0 as usize];
            if info.sealed && *info.module != *cur && !out.contains(d) {
                out.push(*d);
            }
        }
        Tm::App(f, a, ..) => {
            collect_sealed(f, g, cur, out);
            collect_sealed(a, g, cur, out);
        }
        Tm::Pi(_, _, _, a, b) => {
            collect_sealed(a, g, cur, out);
            collect_sealed(b, g, cur, out);
        }
        Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => {
            v.iter().for_each(|x| collect_sealed(x, g, cur, out))
        }
        _ => {}
    }
}
