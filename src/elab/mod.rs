//! Elaboration: surface AST → core terms, with type checking (M1).
//!
//! Bidirectional checking with implicit arguments solved by pattern
//! unification. `match` is compiled to case trees with exhaustiveness
//! checking (D4). Predicates in constraints are type-checked as `Bool` and
//! recorded for the prover (M3).

mod classes;
pub mod complete;
mod decls;
mod expr;
mod eq;
mod interval;
pub mod index;
mod order;
mod pattern;
mod refine;
pub mod stdlib;
mod termination;

use crate::core::*;
use crate::diag::Diagnostic;
use crate::source::{SourceFile, Span};
use crate::syntax::ast;
use std::collections::{BTreeMap, HashMap, HashSet};
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
    /// Where its name is bound, if known (for the index, §15.5).
    pub span: Option<Span>,
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
        self.locals.push(Local { name: Rc::from(name), ty, mult, bound: true, param: None, sub: None, comptime: false, span: None });
        l
    }
    pub fn define(&mut self, name: &str, ty: Val, val: Val, mult: Mult) -> usize {
        let l = self.lvl();
        self.env.push(val);
        self.locals.push(Local { name: Rc::from(name), ty, mult, bound: false, param: None, sub: None, comptime: false, span: None });
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
    /// The function whose body this is in.
    pub owner: Option<DefId>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum OpClass {
    Numeric,
    Ordered,
    Concat,
    HasLen,
    /// `==`/`!=` in compiled code: no functions (D125).
    Comparable,
}

/// A use of a generic function in compiled code: its type parameters'
/// arguments, for D125 (b).
pub struct Inst {
    pub caller: Option<DefId>,
    pub callee: DefId,
    /// The arguments of the callee's leading implicit binders, by position.
    pub args: Vec<Val>,
    pub lvl: usize,
    pub names: Vec<Name>,
    pub span: Span,
}

/// Why a function's type parameter must not be a function type (D125 b):
/// the function that compares it with `==`, and that parameter's name.
#[derive(Clone)]
pub struct EqReq {
    pub root: DefId,
    pub param: Name,
}

/// Predicates recorded for the prover (M3).
/// What an obligation is for; decides how a failure is reported (§7.1).
#[derive(Clone, Debug, PartialEq)]
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
/// Arithmetic whose operands' type wasn't known yet (D134, D135): its
/// result's type (a meta) is settled when it is.
pub struct ArithResult {
    pub result: Val,
    pub operands: Val,
    pub lvl: usize,
    pub op: Prim,
    pub left: Tm,
    pub right: Tm,
    /// Each operand's own type (D135).
    pub left_ty: Val,
    pub right_ty: Val,
}

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
    /// Each loaded module's file, absolute (for tools, §15.5).
    pub paths: HashMap<String, std::path::PathBuf>,
    /// The index of names in the module being checked (§15.5).
    pub index: Vec<index::NameUse>,
    /// That module.
    pub index_of: Option<String>,
    /// Where each global is declared: module and the span of its name.
    pub decl_at: HashMap<index::Target, (String, Span)>,
    /// A declaration's header as written, for hover.
    pub decl_sig: HashMap<index::Target, String>,
    /// `function`, `lemma`, `constant` or `type` (an alias).
    pub def_class: HashMap<DefId, &'static str>,
    pub diags: Vec<(String, Diagnostic)>,
    /// Each module's declarations: span and what they declare (D122).
    pub decl_spans: HashMap<String, Vec<(Span, Option<Sym>)>>,
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
    /// Results of arithmetic whose operands' type wasn't known yet (D134):
    /// the result's type (a meta), the operands' type, the level.
    pub arith_results: Vec<ArithResult>,
    /// The anonymous refinement made for each range (D135).
    pub ranges: HashMap<(Option<i128>, Option<i128>), DefId>,
    /// Inferred `if`s and `match`es whose branches' ranges join (D135).
    pub joins: HashMap<MetaId, interval::Join>,
    /// The type `check` inferred for what it checked, if it did.
    pub last_checked: Option<Val>,
    /// An arithmetic operation's operands' own types (D135).
    pub operand_types: Option<(Val, Val)>,
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
    /// Inside a lemma's proof, which is never compiled (D125).
    pub in_proof: usize,
    /// Type parameters compared with `==` in compiled code, by function and
    /// binder position (D125 b).
    pub eq_reqs: HashMap<DefId, BTreeMap<usize, EqReq>>,
    /// This module's uses of generic functions, resolved after its bodies.
    pub insts: Vec<Inst>,
    /// The last definition `sym_term` gave, for `insert` to record its use.
    pub pending_inst: Option<(DefId, Span)>,
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
    /// Functions recursing by `decreasing` that end without their
    /// preconditions (D118), found while proving.
    pub ends_everywhere: std::sync::Mutex<HashSet<DefId>>,
    /// Heads of saturated calls (recursion through a partial application
    /// can't have its measure checked, E0303).
    pub saturated_heads: HashSet<Span>,
    /// `check` declarations: module, span, elaborated `Bool` term (D40).
    pub checks: Vec<(String, Span, Tm)>,
    /// For a `check` that is an `==`: the type of its sides, so a false one
    /// can show them as values of that type (a `Char` as `c'a'`).
    pub check_eq_tys: HashMap<Span, Tm>,
    /// The operand type of the `==` elaborated last (for `check_eq_tys`).
    pub last_eq_ty: Option<Val>,
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
    /// Classes (D136), by their dictionary's type.
    pub class_defs: HashMap<TyId, classes::ClassDef>,
    /// This module's classes, until their types are registered.
    pub pending_classes: Vec<(String, String, Vec<ast::ClassMember>, Span)>,
    /// This module's instances, until their dictionary functions are registered.
    pub pending_insts: Vec<classes::PendingInst>,
    /// This module's types and their numbers of parameters, for instances' kinds (M25).
    pub local_ty_params: HashMap<String, usize>,
    /// Where each declaration of the module being checked came from.
    pub decl_origin: Vec<classes::Origin>,
    /// Classes' functions: their postconditions are the instances' to prove.
    pub class_methods: HashSet<DefId>,
    /// Classes' lemmas: assumed, each instance proving them.
    pub class_lemmas: HashSet<DefId>,
    /// Functions building an instance's dictionary.
    pub dict_defs: HashSet<DefId>,
    /// Each instance member's dictionary function.
    pub inst_member_of: HashMap<DefId, DefId>,
    /// Instances, by class and the head of their type.
    pub instances: HashMap<(TyId, classes::HeadKey), classes::InstInfo>,
    /// Dictionaries to find once types are known.
    pub inst_reqs: Vec<classes::InstReq>,
    /// Inside a named precondition: `forall` is allowed (D137).
    pub forall_ok: usize,
    /// The named preconditions of the function being checked (D137).
    pub cur_hyps: Vec<(String, Val)>,
    /// The span of the name being elaborated (for a dictionary's errors).
    pub name_span: Span,
    /// Text for spans standing for code written in another module (a class's
    /// signatures in an instance, D136): module, start, end → text.
    pub text_override: HashMap<(String, u32, u32), String>,
    /// Synthetic spans (beyond any file's text, from `SYNTHETIC`), each
    /// standing for the real span it is shown at: module, start → anchor.
    pub synthetic: HashMap<(String, u32), Span>,
    /// Unknowns in a reported type mismatch (D141 c).
    pub blamed: HashSet<MetaId>,
    /// What is known at the cursor, when completing (D142).
    pub completion: Option<complete::CompInfo>,
    /// Completing at this byte of this module: other bodies aren't checked.
    pub completing: Option<(String, u32)>,
}

/// Where synthetic spans start: past the end of any source file.
pub const SYNTHETIC: u32 = 0xC000_0000;

pub struct Failed;

impl Elab {
    pub fn new() -> Elab {
        Elab {
            g: Globals::new(),
            modules: HashMap::new(),
            sources: HashMap::new(),
            diags: Vec::new(),
            decl_spans: HashMap::new(),
            seen: HashSet::new(),
            cur: String::new(),
            loading: Vec::new(),
            base_dir: None,
            user_modules: Vec::new(),
            module_pkg: HashMap::new(),
            deferred: Vec::new(),
            arith_results: Vec::new(),
            ranges: HashMap::new(),
            joins: HashMap::new(),
            last_checked: None,
            operand_types: None,
            fn_meta: HashMap::new(),
            cur_fn: None,
            calls: Vec::new(),
            module_fns: Vec::new(),
            obligations: Vec::new(),
            paths: HashMap::new(),
            index: Vec::new(),
            index_of: None,
            decl_at: HashMap::new(),
            decl_sig: HashMap::new(),
            def_class: HashMap::new(),
            checks: Vec::new(),
            check_eq_tys: HashMap::new(),
            last_eq_ty: None,
            specs: HashMap::new(),
            transparent: HashSet::new(),
            con_invs: HashMap::new(),
            alias_preds: HashMap::new(),
            alias_subject: HashMap::new(),
            result_metas: HashMap::new(),
            arg_of: None,
            in_spec: 0,
            in_proof: 0,
            eq_reqs: HashMap::new(),
            insts: Vec::new(),
            pending_inst: None,
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
            ends_everywhere: Default::default(),
            saturated_heads: HashSet::new(),
            resource_vars: HashMap::new(),
            stdlib_mode: false,
            map_elem_sub: None,
            match_span: Span::default(),
            pm: Default::default(),
            class_defs: HashMap::new(),
            pending_classes: Vec::new(),
            pending_insts: Vec::new(),
            local_ty_params: HashMap::new(),
            decl_origin: Vec::new(),
            class_methods: HashSet::new(),
            class_lemmas: HashSet::new(),
            dict_defs: HashSet::new(),
            inst_member_of: HashMap::new(),
            instances: HashMap::new(),
            inst_reqs: Vec::new(),
            forall_ok: 0,
            cur_hyps: Vec::new(),
            name_span: Span::default(),
            text_override: HashMap::new(),
            synthetic: HashMap::new(),
            blamed: HashSet::new(),
            completion: None,
            completing: None,
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

    /// Record that the unknown `mt` (from `fresh_meta`) stands for the
    /// implicit parameter `x` of the function `head` is (D141).
    pub fn name_meta(&mut self, cx: &Cx, mt: &Tm, x: &Name, dom: &Val, head: &Tm) {
        if x.starts_with('$') || x.is_empty() || &**x == "_" {
            return;
        }
        let mut h = mt;
        let mut spine = 0;
        while let Tm::App(f, ..) = h {
            spine += 1;
            h = f;
        }
        let Tm::Meta(m) = h else { return };
        let mut f = head;
        while let Tm::App(g, ..) = f {
            f = g;
        }
        let owner = match f {
            Tm::Def(d) => Some(self.g.defs[d.0 as usize].name.clone()),
            Tm::Con(c) => Some(self.g.cons[c.0 as usize].name.clone()),
            _ => None,
        };
        // A type (`Type`) or a type constructor (`Type -> Type`, M25).
        let mut arity = 0;
        let mut d = self.force(dom);
        let is_type = loop {
            match d {
                Val::Univ(_) => break true,
                Val::Pi(_, _, _, a, c) if matches!(self.force(&a), Val::Univ(_)) => {
                    arity += 1;
                    d = self.force(&apply_closure(&self.g, &c, Val::var(cx.lvl())));
                }
                _ => break false,
            }
        };
        self.g.meta_origins.borrow_mut().insert(*m, crate::core::MetaOrigin { name: x.clone(), owner, spine, is_type, arity });
    }

    pub fn fresh_meta_val(&mut self, cx: &Cx) -> Val {
        let t = self.fresh_meta(cx);
        self.eval(cx, &t)
    }

    /// A type for a message: computed (`BadPlaceholder`, not the call that
    /// gives it), but a refinement alias by its name (`Nat`, not `Int`).
    pub fn show_written(&self, cx: &Cx, v: &Val) -> String {
        let t = quote(&self.g, cx.lvl(), v);
        match crate::core::head_def(&t) {
            Some(d) if self.alias_preds.contains_key(&d) => self.show_val(cx, v),
            _ => self.show_val(cx, &self.force(v)),
        }
    }

    /// Unify, reporting a type mismatch on failure. Returns false on failure.
    pub fn unify_at(&mut self, cx: &Cx, expected: &Val, actual: &Val, span: Span, what: &str) -> bool {
        match unify(&self.g, cx.lvl(), expected, actual) {
            Ok(()) => true,
            Err(why) => {
                // Show computed types (`BadPlaceholder`, not the call that gives
                // it), but a refinement alias by its name (`U8`, not `Nat`).
                let (e, a) = (self.show_written(cx, expected), self.show_written(cx, actual));
                let (expected, actual) = (&self.force(expected), &self.force(actual));
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
                // A mismatch about an unknown already in a reported one
                // follows from it (D141 c).
                let unknowns = {
                    let mut v = self.unknowns(cx.lvl(), expected);
                    for m in self.unknowns(cx.lvl(), actual) {
                        if !v.contains(&m) {
                            v.push(m);
                        }
                    }
                    v
                };
                if unknowns.iter().any(|m| self.blamed.contains(m)) {
                    return false;
                }
                self.blamed.extend(unknowns.iter().copied());
                let mut d = Diagnostic::error("E0201", format!("type mismatch: expected `{e}`, found `{a}`"), span)
                    .with_label(format!("{what} has type `{a}`"));
                if let Some(n) = self.unknowns_note(&unknowns, why, &e, &a) {
                    d = d.with_note(n);
                }
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

}

impl Elab {
    /// The unknowns in `v` the checker hasn't worked out, in order.
    pub fn unknowns(&self, lvl: usize, v: &Val) -> Vec<MetaId> {
        fn go(g: &Globals, t: &Tm, lvl: usize, out: &mut Vec<MetaId>) {
            match t {
                Tm::Meta(m) => match g.meta(*m) {
                    Some(v) => go(g, &quote(g, lvl, &v), lvl, out),
                    None => {
                        if !out.contains(m) {
                            out.push(*m)
                        }
                    }
                },
                Tm::App(f, a, ..) => {
                    go(g, f, lvl, out);
                    go(g, a, lvl, out);
                }
                Tm::Pi(_, _, _, a, b) => {
                    go(g, a, lvl, out);
                    go(g, b, lvl + 1, out);
                }
                Tm::Lam(_, _, _, b) => go(g, b, lvl + 1, out),
                Tm::TyConApp(_, v) | Tm::TupleTy(v) | Tm::ConApp(_, v) | Tm::Tuple(v) => v.iter().for_each(|x| go(g, x, lvl, out)),
                _ => {}
            }
        }
        let mut out = Vec::new();
        go(&self.g, &quote(&self.g, lvl, v), lvl, &mut out);
        out
    }

    /// What the named unknowns in a message stand for (D141): "`?f` is
    /// `doubled`'s type parameter `f`, a type constructor like `List`", and
    /// why `?f x` can't be the other type.
    fn unknowns_note(&self, unknowns: &[MetaId], why: crate::core::UnifyError, e: &str, a: &str) -> Option<String> {
        let origins = self.g.meta_origins.borrow();
        let named: Vec<&crate::core::MetaOrigin> = unknowns.iter().filter_map(|m| origins.get(m)).collect();
        if named.is_empty() {
            return None;
        }
        // By function, in order of first appearance.
        let mut groups: Vec<(Option<Name>, Vec<&crate::core::MetaOrigin>)> = Vec::new();
        for o in &named {
            match groups.iter_mut().find(|g| g.0 == o.owner) {
                Some(g) => g.1.push(o),
                None => groups.push((o.owner.clone(), vec![o])),
            }
        }
        let not_applied = match why {
            crate::core::UnifyError::NotApplied(m) => origins.get(&m).map(|o| {
                let shown = format!("?{}", o.name);
                // The side without the unknown.
                if e.contains(&shown) { a.to_string() } else { e.to_string() }
            }),
            crate::core::UnifyError::Mismatch => None,
        };
        let mut parts = Vec::new();
        for (owner, os) in &groups {
            let unk = os.iter().map(|o| format!("`?{}`", o.name)).collect::<Vec<_>>();
            let params = os.iter().map(|o| format!("`{}`", o.name)).collect::<Vec<_>>();
            let kind = if os.iter().all(|o| o.is_type) { "type parameter" } else { "implicit parameter" };
            let whose = match owner {
                Some(f) => format!("`{f}`'s "),
                None => String::new(),
            };
            let mut p = if os.len() == 1 {
                format!("{} is {whose}{kind} {}", unk[0], params[0])
            } else {
                format!("{} are {whose}{kind}s {}", and_list(&unk), and_list(&params))
            };
            if os.len() == 1 && os[0].arity > 0 {
                p += ", a type constructor like `List`";
            }
            parts.push(p);
        }
        let mut note = parts.join("; ");
        if let Some(other) = not_applied {
            let one = named.len() == 1 && named[0].arity > 0;
            note += &if one { format!("; `{other}` isn't one applied to a type") } else { format!("; `{other}` isn't a type constructor applied to a type") };
        }
        Some(note)
    }
}

/// `a`, `a and b`, `a, b and c`.
fn and_list(xs: &[String]) -> String {
    match xs {
        [] => String::new(),
        [x] => x.clone(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
    }
}

/// A type constructor applied to arguments, in either shape the elaborator builds.
fn tycon_app(t: &Tm) -> Option<(TyId, Vec<&Tm>)> {
    match t {
        Tm::TyCon(id) => Some((*id, Vec::new())),
        Tm::TyConApp(id, args) => Some((*id, args.iter().collect())),
        Tm::App(..) => {
            let mut args = Vec::new();
            let mut h = t;
            while let Tm::App(f, a, ..) = h {
                args.push(&**a);
                h = f;
            }
            match h {
                Tm::TyCon(id) => {
                    args.reverse();
                    Some((*id, args))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Whether a type declaration holds a resource.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lin {
    No,
    Yes,
    Depends,
}

impl Lin {
    fn or(self, o: Lin) -> Lin {
        match (self, o) {
            (Lin::Yes, _) | (_, Lin::Yes) => Lin::Yes,
            (Lin::Depends, _) | (_, Lin::Depends) => Lin::Depends,
            _ => Lin::No,
        }
    }

    fn of(b: bool) -> Lin {
        if b { Lin::Yes } else { Lin::No }
    }
}

impl Elab {
    /// A primitive resource (D39): implemented by the runtime as an open, stateful thing.
    fn is_primitive_resource(&self, t: TyId) -> bool {
        let ti = &self.g.tys[t.0 as usize];
        matches!((&*ti.module, &*ti.name), ("std.files", "File") | ("std.proc", "Child"))
    }

    /// Does this type declaration contain a resource (in a constructor field)?
    /// A cown or future owns its contents; its handle may be shared (D39).
    fn is_owner(&self, t: TyId) -> bool {
        Some(t) == self.g.well_known.cown || Some(t) == self.g.well_known.future
    }

    /// Is a type declared with a resource in a constructor field (D39)? `Depends`
    /// when a field's type is computed from the parameters (`pipe_end ss.stdout`,
    /// D112): then it is a resource for some arguments and not others.
    fn ty_lin(&self, t: TyId, visiting: &mut Vec<TyId>) -> Lin {
        if self.is_primitive_resource(t) {
            return Lin::Yes;
        }
        if self.is_owner(t) || visiting.contains(&t) {
            return Lin::No;
        }
        visiting.push(t);
        let ti = &self.g.tys[t.0 as usize];
        let mut r = Lin::No;
        for c in &ti.ctors {
            for f in &self.g.cons[c.0 as usize].fields {
                if f.1 != Mult::Zero {
                    r = r.or(self.field_lin(&f.3, visiting));
                }
            }
        }
        visiting.pop();
        r
    }

    /// A field's type, in the context of the parameters and earlier fields.
    fn field_lin(&self, t: &Tm, visiting: &mut Vec<TyId>) -> Lin {
        if let Some((id, args)) = tycon_app(t) {
            if self.is_owner(id) {
                return Lin::No;
            }
            return args.iter().fold(self.ty_lin(id, visiting), |r, a| r.or(self.field_lin(a, visiting)));
        }
        match t {
            Tm::TyCon(id) => self.ty_lin(*id, visiting),
            Tm::TyConApp(id, args) => {
                if self.is_owner(*id) {
                    return Lin::No;
                }
                args.iter().fold(self.ty_lin(*id, visiting), |r, a| r.or(self.field_lin(a, visiting)))
            }
            Tm::TupleTy(ts) => ts.iter().fold(Lin::No, |r, a| r.or(self.field_lin(a, visiting))),
            Tm::Meta(m) => match self.g.meta(*m) {
                Some(v) => Lin::of(self.val_linear(&v)),
                None => Lin::No,
            },
            // A type variable: a generic container (D45), decided by its argument.
            Tm::Var(_) | Tm::Pi(..) | Tm::Univ(_) | Tm::Lit(_) | Tm::Error => Lin::No,
            // A proposition (a refinement field) or a value: never a resource.
            _ if !self.computes_type(t) => Lin::No,
            // Computed: an alias, an application, a match.
            _ => {
                let mut fv = std::collections::BTreeSet::new();
                crate::core::free_vars(t, 0, &mut fv);
                if fv.is_empty() {
                    Lin::of(self.val_linear(&eval(&self.g, &Rc::new(Vec::new()), t)))
                } else {
                    Lin::Depends
                }
            }
        }
    }

    fn tm_linear(&self, t: &Tm, visiting: &mut Vec<TyId>) -> bool {
        if let Some((id, args)) = tycon_app(t) {
            if self.is_owner(id) {
                return false;
            }
            return match self.ty_lin(id, visiting) {
                Lin::Yes => true,
                Lin::No => args.iter().any(|a| self.tm_linear(a, visiting)),
                // Decided by the arguments: evaluate them if they are known.
                Lin::Depends => self.closed_linear(t),
            };
        }
        match t {
            Tm::TyCon(id) => self.ty_lin(*id, visiting) != Lin::No,
            Tm::TyConApp(id, args) => {
                if self.is_owner(*id) {
                    return false;
                }
                match self.ty_lin(*id, visiting) {
                    Lin::Yes => true,
                    Lin::No => args.iter().any(|a| self.tm_linear(a, visiting)),
                    // Decided by the arguments: evaluate them if they are known.
                    Lin::Depends => self.closed_linear(t),
                }
            }
            Tm::TupleTy(ts) => ts.iter().any(|a| self.tm_linear(a, visiting)),
            Tm::Meta(m) => match self.g.meta(*m) {
                Some(v) => self.val_linear(&v),
                None => false,
            },
            Tm::Var(_) | Tm::Pi(..) | Tm::Univ(_) | Tm::Lit(_) | Tm::Error => false,
            _ if !self.computes_type(t) => false,
            _ => self.closed_linear(t),
        }
    }

    /// A computed type: decided by evaluating it if it mentions no variables,
    /// else a resource, since it may be one (D112).
    fn closed_linear(&self, t: &Tm) -> bool {
        let mut fv = std::collections::BTreeSet::new();
        crate::core::free_vars(t, 0, &mut fv);
        if fv.is_empty() {
            self.val_linear(&eval(&self.g, &Rc::new(Vec::new()), t))
        } else {
            true
        }
    }

    /// Is a value of this type linear (D39)?
    pub fn val_linear(&self, v: &Val) -> bool {
        self.val_linear_at(v, 0)
    }

    fn val_linear_at(&self, v: &Val, depth: usize) -> bool {
        if depth > 32 {
            return true;
        }
        match self.force(v) {
            Val::TyCon(id, args) => {
                if self.is_owner(id) {
                    return false;
                }
                match self.ty_lin(id, &mut Vec::new()) {
                    Lin::Yes => true,
                    Lin::No => args.iter().any(|a| self.val_linear_at(a, depth + 1)),
                    Lin::Depends => self.fields_linear(id, &args, depth),
                }
            }
            Val::TupleTy(ts) => ts.iter().any(|a| self.val_linear_at(a, depth + 1)),
            // A type variable is generic (D45); a stuck computation of a type may be a resource.
            Val::Neutral(Head::Def(d), _) => self.def_gives_type(d),
            Val::Neutral(..) => false,
            _ => false,
        }
    }

    pub fn type_linear(&self, t: &Tm) -> bool {
        self.tm_linear(t, &mut Vec::new())
    }

    /// Could this term (in a type position) compute a type, rather than a
    /// proposition or a value? Only an application of a definition whose
    /// result is a type, or something we can't see into (a field, a match).
    fn computes_type(&self, t: &Tm) -> bool {
        let mut h = t;
        while let Tm::App(f, ..) = h {
            h = f;
        }
        match h {
            Tm::Def(d) => self.def_gives_type(*d),
            Tm::Field(..) | Tm::Proj(..) | Tm::Case(..) | Tm::Let(..) => true,
            _ => false,
        }
    }

    /// Is `d`'s result (after all its parameters) a universe?
    fn def_gives_type(&self, d: DefId) -> bool {
        let mut t = &self.g.defs[d.0 as usize].ty;
        while let Tm::Pi(_, _, _, _, b) = t {
            t = b;
        }
        matches!(t, Tm::Univ(_))
    }

    /// The fields of `id` at these arguments: is any a resource?
    fn fields_linear(&self, id: TyId, args: &[Val], depth: usize) -> bool {
        let ti = &self.g.tys[id.0 as usize];
        for c in &ti.ctors {
            let mut env: Vec<Val> = args.to_vec();
            for (k, f) in self.g.cons[c.0 as usize].fields.iter().enumerate() {
                let ty = eval(&self.g, &Rc::new(env.clone()), &f.3);
                if f.1 != Mult::Zero && self.field_lin(&f.3, &mut Vec::new()) != Lin::No && self.val_linear_at(&ty, depth + 1) {
                    return true;
                }
                // Earlier fields are unknown here: fresh variables far above any context.
                env.push(Val::var(usize::MAX / 2 + k));
            }
        }
        false
    }

    /// The multiplicity for a variable the program names: linear types make it `own` (D39).
    pub fn named_mult(&mut self, cx: &Cx, name: &str, ty: &Val, span: Span, declared: Mult) -> Mult {
        if declared != Mult::Many || name == "_" || name.starts_with('$') || !self.val_linear(ty) {
            return declared;
        }
        if let Some(f) = self.cur_fn {
            let shown = self.show_resource(cx, ty);
            self.resource_vars.insert((f, name.to_string()), (span, shown));
        }
        Mult::One
    }

    /// A resource's type for a message: a computed type (`pipe_end Pipe`) is
    /// shown as what it computes to (`File`); an alias keeps its name.
    pub fn show_resource(&self, cx: &Cx, ty: &Val) -> String {
        match force_meta(&self.g, ty.clone()) {
            Val::Neutral(Head::Def(_), _) | Val::Neutral(Head::Prim(..), _) => {
                let f = self.force(ty);
                if matches!(f, Val::TyCon(..) | Val::TupleTy(_)) {
                    return self.show_val(cx, &f);
                }
                self.show_val(cx, ty)
            }
            _ => self.show_val(cx, ty),
        }
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
        // In a specification only a callee's precondition is checked: a spec
        // mustn't speak of a call that can't be made (M17, D118). A
        // specification elaborated twice (a lemma's `ensures`) obliges once.
        if self.in_spec > 0 {
            if !matches!(kind, ObKind::Pre { .. }) {
                return;
            }
            if self.obligations.iter().any(|o| o.span == span && o.module == self.cur && o.kind == kind) {
                return;
            }
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
    /// D121 (c): `v` is a `Nat` by construction, with no obligation: a
    /// non-negative literal, a `Nat` local, `len`, `+`, `*`, `/` or `%` of
    /// such values, or a `Nat` subtraction (which has its own obligation).
    pub fn nat_by_closure(&self, cx: &Cx, v: &Val) -> bool {
        match crate::core::force_meta(&self.g, v.clone()) {
            Val::Lit(Lit::Num(n)) => n >= 0,
            Val::Neutral(Head::Var(l), sp) if sp.is_empty() => {
                cx.locals.get(l).is_some_and(|x| crate::core::is_nat(&self.g, &x.ty))
            }
            Val::Neutral(Head::Prim(p, args), sp) if sp.is_empty() => match p {
                Prim::Add | Prim::Mul | Prim::Div | Prim::Rem => args.iter().take(2).all(|a| self.nat_by_closure(cx, a)),
                Prim::Sub => args.get(2).is_some_and(|t| crate::core::is_nat(&self.g, t)),
                Prim::Len => true,
                _ => false,
            },
            v @ Val::Neutral(..) => {
                // An `if` or `match` whose every branch is a `Nat` (a branch's
                // own fields are unknown here, so one that uses them is not).
                if let Val::Neutral(_, sp) = &v {
                    if let Some(Elim::Case(ct, env)) = sp.last() {
                        let at = |n: usize, body: &crate::core::Tm| {
                            let mut e = (**env).clone();
                            e.extend(std::iter::repeat_n(Val::Error, n));
                            self.nat_by_closure(cx, &eval(&self.g, &Rc::new(e), body))
                        };
                        if ct.branches.iter().all(|(_, n, b)| at(*n, b))
                            && ct.lits.iter().all(|(_, b)| at(0, b))
                            && ct.default.as_ref().is_none_or(|d| at(0, d))
                        {
                            return true;
                        }
                    }
                }
                // A record field whose type is `Nat`.
                if let Val::Neutral(_, sp) = &v {
                    if let Some(Elim::Field(c, i)) = sp.last() {
                        let fty = &self.g.cons[c.0 as usize].fields[*i].3;
                        let np = self.g.arity_ty(self.g.cons[c.0 as usize].ty);
                        // Only a type that mentions no parameter or earlier field.
                        let mut free = std::collections::BTreeSet::new();
                        crate::core::free_vars(fty, 0, &mut free);
                        if free.is_empty() && crate::core::is_nat(&self.g, &eval(&self.g, &Rc::new(vec![Val::Error; np + i]), fty)) {
                            return true;
                        }
                    }
                }
                // A call of a function (global or local) whose result type is `Nat`.
                let call = match &v {
                    Val::Neutral(Head::Def(d), sp) => {
                        let ty = eval(&self.g, &Rc::new(Vec::new()), &self.g.defs[d.0 as usize].ty);
                        self.returns_nat(&ty, sp)
                    }
                    Val::Neutral(Head::Var(l), sp) => cx.locals.get(*l).is_some_and(|x| self.returns_nat(&x.ty, sp)),
                    _ => false,
                };
                // Or what a `Nat` local stands for (`j` in `Some (n, j)`, a
                // `let` of a `match`).
                call || {
                    let t = quote(&self.g, cx.lvl(), &v);
                    cx.locals.iter().zip(cx.env.iter()).any(|(x, e)| {
                        crate::core::is_nat(&self.g, &x.ty) && crate::core::tm_eq(&quote(&self.g, cx.lvl(), e), &t)
                    })
                }
            }
            _ => false,
        }
    }

    /// Does a function of type `ty`, applied as `sp` says, return a `Nat`?
    fn returns_nat(&self, ty: &Val, sp: &[Elim]) -> bool {
        let mut t = ty.clone();
        for e in sp {
            let Elim::App(a, _) = e else { return false };
            match crate::core::force(&self.g, t) {
                Val::Pi(_, _, _, _, c) => t = apply_closure(&self.g, &c, a.clone()),
                _ => return false,
            }
        }
        crate::core::is_nat(&self.g, &t)
    }

    /// A predicate that only says "is a `Nat`" of a value that is one by
    /// construction (D121 c) needs no obligation.
    pub fn nat_pred_holds(&self, cx: &Cx, p: &Pred, v: &Val) -> bool {
        matches!(p.alias, Some((_, d)) if Some(d) == self.g.well_known.nat) && self.nat_by_closure(cx, v)
    }

    pub fn oblige_posts_at(&mut self, cx: &Cx, v: Val, at: Span) {
        self.oblige_posts_typed(cx, v, at, None)
    }

    /// The same, knowing the returned value's type: one already a `Nat`
    /// meets a `Nat` result (D121).
    pub fn oblige_posts_typed(&mut self, cx: &Cx, v: Val, at: Span, ty: Option<&Val>) {
        let Some(pt) = self.post_target.clone() else { return };
        let mut env = pt.binders.clone();
        env.push(v.clone());
        let typed_nat = ty.is_some_and(|t| crate::core::is_nat(&self.g, t));
        for p in &pt.posts {
            let nat_pred = matches!(p.alias, Some((_, d)) if Some(d) == self.g.well_known.nat);
            if self.nat_pred_holds(cx, p, &v) || (nat_pred && typed_nat) {
                continue;
            }
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
        if let Some(t) = self.text_override.get(&(self.cur.clone(), span.start, span.end)) {
            return t.clone();
        }
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

    /// `Nat`, the prelude's refinement of `Int` (D121).
    pub fn nat(&self) -> Val {
        match self.g.well_known.nat {
            Some(d) => eval(&self.g, &Rc::new(Vec::new()), &Tm::Def(d)),
            None => self.int(),
        }
    }
    /// The prelude's `Char` (a refinement of `Nat`), the type of `c'…'` (D19).
    pub fn char_ty(&self) -> Val {
        self.prelude_alias("Char")
    }
    /// The prelude's `U8`, the type of `'x'` (D19).
    pub fn u8_ty(&self) -> Val {
        self.prelude_alias("U8")
    }
    fn prelude_alias(&self, name: &str) -> Val {
        let d = self.g.defs.iter().position(|i| i.module.as_ref() == "std.prelude" && i.name.as_ref() == name);
        match d {
            Some(d) => eval(&self.g, &Rc::new(Vec::new()), &Tm::Def(DefId(d as u32))),
            None => self.int(),
        }
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
    /// `Bytes`, the alias of `Array U8` (D133).
    pub fn bytes(&self) -> Val {
        match self.g.well_known.bytes {
            Some(d) => eval(&self.g, &Rc::new(Vec::new()), &Tm::Def(d)),
            None => Val::Error,
        }
    }
    pub fn array_of(&self, elem: Val) -> Val {
        self.ty_val(self.g.well_known.array, vec![elem])
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
        // The result of arithmetic (D134): settle its operands' type first.
        let pos = self.arith_results.iter().position(|a| matches!(self.force(&a.result), Val::Neutral(Head::Meta(m2), _) if m2 == m));
        if let Some(pos) = pos {
            let a = self.arith_results.remove(pos);
            self.default_if_numeric(&a.operands);
            self.settle_arith(a);
            return true;
        }
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

    /// The type of `+ - * / %` on operands of type `ty` (D134): `Nat` for
    /// `Nat` and its refinements, `Int` for any other number type.
    pub fn arith_base(&self, ty: &Val) -> Val {
        if crate::core::is_nat(&self.g, ty) {
            return self.nat();
        }
        match self.force(ty) {
            Val::TyCon(id, _) if Some(id) == self.g.well_known.int => self.int(),
            _ => ty.clone(),
        }
    }

    /// The type of `lt op rt` on operands of type `ty`, now or, if `ty`
    /// isn't known yet, once it is (D134, D135).
    #[allow(clippy::too_many_arguments)]
    pub fn arith_result(&mut self, cx: &Cx, op: Prim, lt: &Tm, rt: &Tm, ty: &Val, lty: &Val, rty: &Val) -> Val {
        if let Val::Neutral(Head::Meta(_), _) = self.force(ty) {
            let r = self.fresh_meta_val(cx);
            self.arith_results.push(ArithResult {
                result: r.clone(),
                operands: ty.clone(),
                lvl: cx.lvl(),
                op,
                left: lt.clone(),
                right: rt.clone(),
                left_ty: lty.clone(),
                right_ty: rty.clone(),
            });
            return r;
        }
        self.arith_type(op, lt, rt, ty, lty, rty)
    }

    fn settle_arith(&mut self, a: ArithResult) {
        let t = self.arith_type(a.op, &a.left, &a.right, &a.operands, &a.left_ty, &a.right_ty);
        let _ = unify(&self.g, a.lvl, &a.result, &t);
    }

    pub fn solve_deferred(&mut self) {
        self.solve_instances(false);
        let ds = std::mem::take(&mut self.deferred);
        for d in &ds {
            if let Val::Neutral(Head::Meta(_), _) = self.force(&d.ty) {
                if matches!(d.kind, OpClass::Numeric | OpClass::Ordered) {
                    let n = self.nat();
                    let _ = unify(&self.g, d.lvl, &d.ty, &n);
                }
            }
        }
        for a in std::mem::take(&mut self.arith_results) {
            self.settle_arith(a);
        }
        self.solve_instances(true);
        for d in ds {
            if d.kind == OpClass::Comparable {
                self.solve_comparable(&d);
                continue;
            }
            let t = self.force(&d.ty);
            let wk = &self.g.well_known;
            let ok = match (&t, d.kind) {
                (Val::Error, _) => true,
                (Val::Neutral(Head::Meta(_), _), _) => true,
                (Val::TyCon(id, _), OpClass::Numeric | OpClass::Ordered) => {
                    Some(*id) == wk.int
                }
                (Val::TyCon(id, _), OpClass::Concat | OpClass::HasLen) => {
                    Some(*id) == wk.string || Some(*id) == wk.array || Some(*id) == wk.list
                }
                _ => false,
            };
            if !ok {
                // A refinement alias by its name (`Small`, not `Nat`), as in E0201.
                let declared = quote(&self.g, d.lvl, &d.ty);
                let shown_tm = match crate::core::head_def(&declared) {
                    Some(a) if self.alias_preds.contains_key(&a) => declared,
                    _ => quote(&self.g, d.lvl, &t),
                };
                let shown = show(&self.g, &d.names, &shown_tm);
                let need = match d.kind {
                    OpClass::Numeric => "numbers (`Nat` or `Int`)",
                    OpClass::Ordered => "numbers (`Nat` or `Int`) to compare",
                    OpClass::Concat => "a `String`, `List` or `Array`",
                    OpClass::HasLen => "a `String`, `List` or `Array`",
                    OpClass::Comparable => unreachable!(),
                };
                let mut diag = Diagnostic::error("E0210", format!("{} needs {need}, but this is `{shown}`", d.what), d.span)
                    .with_label(format!("has type `{shown}`"));
                if d.what == "`+`" && matches!(&t, Val::TyCon(id, _) if Some(*id) == wk.string || Some(*id) == wk.array || Some(*id) == wk.list) {
                    diag = diag.with_help("to join strings, lists or arrays, use `++`");
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
    check_module_at(name_hint, file, m, dir, None)
}

/// `check_module`; completing at byte `at` (D142), only the body there is
/// checked, and other modules' signatures.
pub fn check_module_at(name_hint: &str, file: &SourceFile, m: &ast::Module, dir: Option<&std::path::Path>, at: Option<u32>) -> Elab {
    let mut e = Elab::new();
    if let Some(at) = at {
        let name = m.name.as_ref().map(|q| q.dotted()).unwrap_or_else(|| name_hint.to_string());
        e.completing = Some((name, at));
    }
    e.base_dir = dir.map(|d| d.to_path_buf());
    // Core stdlib modules are always loaded: they define well-known types.
    for core in ["std.prelude", "std.cown", "std.future", "std.system"] {
        e.load_stdlib(core);
    }
    let name = m.name.as_ref().map(|q| q.dotted()).unwrap_or_else(|| name_hint.to_string());
    e.sources.insert(name.clone(), SourceFile::new(file.name.clone(), file.text.clone()));
    e.index_of = Some(name.clone());
    e.elab_module(&name, m, false);
    e
}

impl Elab {
    /// Check as far as possible past errors (D122): set aside the obligations
    /// and `check`s of declarations with errors, and those that mention a
    /// definition or type with errors (or one that uses such, transitively).
    /// `extra` adds errors not in `diags`: the checked file's syntax errors.
    pub fn set_aside_broken(&mut self, extra: &[(String, Span)]) {
        let mut errs: Vec<(String, Span)> =
            self.diags.iter().filter(|(_, d)| d.is_error()).map(|(m, d)| (m.clone(), d.span)).collect();
        errs.extend_from_slice(extra);
        if errs.is_empty() {
            return;
        }
        let mut spans: HashMap<String, Vec<Span>> = HashMap::new();
        let mut defs: HashSet<DefId> = HashSet::new();
        let mut tys: HashSet<TyId> = HashSet::new();
        for (m, sp) in &errs {
            for (d, id) in self.decl_spans.get(m).map(|v| v.as_slice()).unwrap_or(&[]) {
                if d.start <= sp.start && sp.start < d.end.max(d.start + 1) {
                    spans.entry(m.clone()).or_default().push(*d);
                    match id {
                        Some(Sym::Def(x)) => {
                            defs.insert(*x);
                        }
                        Some(Sym::Ty(t)) => {
                            tys.insert(*t);
                        }
                        _ => {}
                    }
                }
            }
        }
        // Close over uses: a definition whose type or body mentions a broken
        // one is broken too (for `check`s, which run it, and proofs, which
        // may unfold it).
        loop {
            let before = defs.len() + tys.len();
            for (k, info) in self.g.defs.iter().enumerate() {
                let d = DefId(k as u32);
                if !defs.contains(&d) && (touches(&info.ty, &self.g, &defs, &tys) || info.body.as_ref().is_some_and(|b| touches(b, &self.g, &defs, &tys))) {
                    defs.insert(d);
                }
            }
            for c in &self.g.cons {
                if !tys.contains(&c.ty) && c.fields.iter().any(|f| touches(&f.3, &self.g, &defs, &tys)) {
                    tys.insert(c.ty);
                }
            }
            if defs.len() + tys.len() == before {
                break;
            }
        }
        let inside = |m: &str, at: Span| spans.get(m).is_some_and(|v| v.iter().any(|d| d.start <= at.start && at.start < d.end));
        let g = &self.g;
        self.checks.retain(|(m, at, t)| !inside(m, *at) && !touches(t, g, &defs, &tys));
        self.obligations.retain(|o| {
            if inside(&o.module, o.span) {
                return false;
            }
            let lvl = o.ctx.len();
            let bad = |v: &Val| touches(&quote(g, lvl, v), g, &defs, &tys);
            !(bad(&o.goal)
                || o.facts.iter().any(bad)
                || o.only_if_nat.as_ref().is_some_and(bad)
                || o.ctx.iter().enumerate().any(|(i, l)| {
                    touches(&quote(g, i, &l.ty), g, &defs, &tys) || l.def.as_ref().is_some_and(|v| touches(&quote(g, i, v), g, &defs, &tys))
                }))
        });
    }
}

/// Whether `t` mentions an error, one of `defs`, or one of `tys` or their constructors.
fn touches(t: &Tm, g: &Globals, defs: &HashSet<DefId>, tys: &HashSet<TyId>) -> bool {
    let go = |x: &Tm| touches(x, g, defs, tys);
    let con = |c: &ConId| tys.contains(&g.cons[c.0 as usize].ty);
    match t {
        Tm::Error => true,
        Tm::Def(d) => defs.contains(d),
        Tm::TyCon(ty) => tys.contains(ty),
        Tm::Con(c) => con(c),
        Tm::Var(_) | Tm::Meta(_) | Tm::Univ(_) | Tm::Lit(_) => false,
        Tm::Pi(_, _, _, a, b) | Tm::App(a, b, ..) => go(a) || go(b),
        Tm::Lam(_, _, _, b) | Tm::Proj(b, _) => go(b),
        Tm::Field(b, c, _) => con(c) || go(b),
        Tm::Let(_, _, a, b, c) => go(a) || go(b) || go(c),
        Tm::TyConApp(ty, v) => tys.contains(ty) || v.iter().any(go),
        Tm::ConApp(c, v) => con(c) || v.iter().any(go),
        Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => v.iter().any(go),
        Tm::Case(s, c) => {
            go(s)
                || c.branches.iter().any(|(k, _, b)| con(k) || go(b))
                || c.lits.iter().any(|(_, b)| go(b))
                || c.default.as_ref().is_some_and(go)
        }
    }
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
