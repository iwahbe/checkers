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
mod descr;
mod eq;
mod interval;
pub mod index;
mod order;
mod pattern;
pub use pattern::BINDING_HELP;
mod refine;
mod template;
pub mod stdlib;
pub mod termination;
pub mod unused;

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
    /// The overloaded built-in `len` (D38)
    Len,
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

/// The binder of explicit parameter `k`, given the leading implicit
/// binders and the implicit ones among the explicit (#161).
pub fn expl_binder(n_implicit: usize, inner: &[usize], k: usize) -> usize {
    let mut b = n_implicit + k;
    for i in inner {
        if *i <= b {
            b += 1;
        }
    }
    b
}

/// The explicit parameter binder `b` is, if it is one.
pub fn expl_index(n_implicit: usize, inner: &[usize], b: usize) -> Option<usize> {
    if b < n_implicit || inner.contains(&b) {
        return None;
    }
    Some(b - n_implicit - inner.iter().filter(|i| **i < b).count())
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
    /// Implicit binders among the explicit ones (#161): see `Sig`.
    pub inner: Vec<usize>,
    pub builtin: bool,
    /// The result's name, if it has one (`-> y`).
    pub result: Option<String>,
}

impl FnMeta {
    /// Its binders: implicit and explicit.
    pub fn n_binders(&self) -> usize {
        self.n_implicit + self.inner.len() + self.params.len()
    }
}

#[derive(Clone, Debug)]
pub struct CallRec {
    pub caller: DefId,
    pub callee: DefId,
    /// For each explicit argument: Some(p) if it is a strict structural subterm of the caller's parameter p.
    pub args: Vec<Option<usize>>,
    /// For each explicit argument: Some(p) if it is the caller's parameter p
    /// itself, passed on unchanged (#109).
    pub same: Vec<Option<usize>>,
    pub span: Span,
    /// `(i, c)`: `args[i]` holds only if condition `c` does (an element
    /// promise read from a body, decided once the module's bodies are
    /// checked; #102). Otherwise `args[i]` is `None`.
    pub conds: Vec<(usize, u32)>,
}

/// Where a function value passed to a call gets its argument (#102): a
/// strict part of the caller's parameter `p`, if condition `cond` holds
/// (`None`: it does, from the callee's signature).
#[derive(Clone, Copy, Debug)]
pub struct ElemSub {
    pub p: usize,
    pub cond: Option<u32>,
}

/// One use of a parameter in a function's body (#102): the parameters `j`
/// it is a function called only with strict parts of here, each if a
/// condition holds. Empty: any other use, which promises nothing.
pub type ParamUse = Vec<(usize, Option<u32>)>;

/// A promise `(callee, k, j)`: `k` is called only with strict parts of `j` (#102).
pub type ElemAlt = (DefId, usize, usize);

/// A function parameter's precondition `pred … j … x …` (#102): `k` and
/// `j` are explicit parameters of the function; `c` and `s` are the
/// explicit argument positions of `pred` that `j` and the subject fill.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ElemPromise {
    pub k: usize,
    pub j: usize,
    pub pred: DefId,
    pub c: usize,
    pub s: usize,
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
    /// ... if this condition holds (an element of a list passed to a
    /// function whose promise is read from its body, #102).
    pub sub_cond: Option<u32>,
    /// Known at compile time (§8.9): a `comptime` parameter, or a field of one.
    pub comptime: bool,
    /// Where its name is bound, if known (for the index, §15.5).
    pub span: Option<Span>,
    /// A parameter whose refinements mention later parameters (#102): its
    /// type with them, which a use of it has. `ty` is the type without
    /// them, over the locals before it, as every local's type is.
    pub refined: Option<Val>,
}

#[derive(Clone, Default)]
pub struct Cx {
    /// Shared, so that evaluating under the context doesn't copy it.
    pub env: Rc<Vec<Val>>,
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
        self.env.clone()
    }
    /// The type a use of local `l` has: with the refinements that mention
    /// later parameters, for such a parameter (#102).
    pub fn ty_of(&self, l: usize) -> Val {
        self.locals[l].refined.clone().unwrap_or_else(|| self.locals[l].ty.clone())
    }
    pub fn names(&self) -> Vec<Name> {
        self.locals.iter().map(|l| l.name.clone()).collect()
    }
    pub fn bind(&mut self, name: &str, ty: Val, mult: Mult) -> usize {
        let l = self.lvl();
        Rc::make_mut(&mut self.env).push(Val::var(l));
        self.locals.push(Local { name: Rc::from(name), ty, mult, bound: true, param: None, sub: None, sub_cond: None, comptime: false, span: None, refined: None });
        l
    }
    pub fn define(&mut self, name: &str, ty: Val, val: Val, mult: Mult) -> usize {
        let l = self.lvl();
        Rc::make_mut(&mut self.env).push(val);
        self.locals.push(Local { name: Rc::from(name), ty, mult, bound: false, param: None, sub: None, sub_cond: None, comptime: false, span: None, refined: None });
        l
    }
    pub fn pop(&mut self) {
        Rc::make_mut(&mut self.env).pop();
        self.locals.pop();
        let n = self.locals.len();
        self.facts.retain(|(l, _)| *l <= n);
    }
    pub fn truncate(&mut self, n: usize) {
        Rc::make_mut(&mut self.env).truncate(n);
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
#[derive(Clone)]
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

/// A function parameter of a class's function, at a refinement alias,
/// that the instance may give values of the class's type to (#226), with
/// where it gives them, as a message says it.
#[derive(Clone, Debug, PartialEq)]
pub struct AliasParam {
    pub name: String,
    /// What the instance may give it, at its first place where it isn't of
    /// the alias: `a value that isn't a `Nat``, `a function whose results
    /// aren't `Nat`s`.
    pub gives: String,
    /// What it must be given instead: `` `Nat`s ``, `functions whose
    /// results are `Nat`s`.
    pub only: String,
    /// The type of the values it is given at the base (`Int`, `Int ->
    /// Int`), and, where those aren't the alias itself, its type at the
    /// alias, a signature for it that would do.
    pub accepts: String,
    pub example: Option<String>,
}

/// Predicates recorded for the prover (M3).
/// What an obligation is for; decides how a failure is reported (§7.1).
#[derive(Clone, Debug, PartialEq)]
pub enum ObKind {
    Pre { callee: String },
    Post { func: String, at: Span },
    Invariant { con: String },
    /// A condition on a type's parameters, where the type is applied (#136):
    /// the type's name and the application as written.
    TypeParams { ty: String, written: String },
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
    /// A predicate on a class's type, for every value of the type an
    /// instance gives it (#176): the class's type (`Encoding.Unit`) and the
    /// type given (`Nat`).
    ClassType { name: String, given: String },
    /// An instance's function with a signature of its own (#225): a
    /// precondition of it that the class's don't imply (`pre`), or a
    /// postcondition of the class's that the instance's don't imply. The
    /// class's declaration of the function, as written.
    Refines { class: String, member: String, pre: bool, declared: String },
    /// A class used at a refinement alias runs the instance of the type the
    /// alias stands for (#226): a value of the class's type that instance
    /// gives must be of the alias. The class, the alias and its type, the
    /// class's function; where the use is a call, its text, else the
    /// function's parameter the instance may give values of the type to
    /// (`param`), or neither: a result, at any arguments. `inside`: a
    /// value inside the result (`Some`'s), not the result itself.
    /// `whole`: a part of the result checked as one (under a recursive
    /// type, or a function): its type at the alias and at the base.
    AtAlias { class: String, alias: String, base: String, member: String, call: Option<String>, param: Option<AliasParam>, inside: bool, whole: Option<(String, String)> },
    Auto,
    Have,
    /// A case a `match` leaves out can't occur there (D144 e): its pattern.
    /// `binding`: the pattern of a `let`, a lambda's parameter or `<-`,
    /// not a `match`.
    Uncovered { case: String, binding: bool },
}

/// Where a branch was entered, asked whether it can be reached (D144 d).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProbeKind {
    /// A `match` arm, at its pattern.
    Arm,
    /// An `if`'s first branch, at its condition.
    Then,
    /// An `if`'s `else` branch, at its condition.
    Else,
}

/// A branch to report if its facts contradict each other (W022).
#[derive(Clone)]
pub struct Probe {
    pub ob: Obligation,
    pub kind: ProbeKind,
    /// The code the branch runs: a branch inside one reported isn't reported.
    pub region: Span,
    /// How many of the facts were in scope before the `match` or `if`.
    pub before: usize,
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
    /// Its type with refinements that mention later locals (#102).
    pub refined: Option<Val>,
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
    /// Each operand's value, if it is a constant: all the result's type
    /// needs of the operand terms, which can be long (`1 + 1 + …`).
    pub left: Option<i128>,
    pub right: Option<i128>,
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
    /// Parameters whose refinements mention later parameters (#102).
    pub late: Vec<Late>,
    /// Explicit parameter `k` is a function whose precondition is a
    /// predicate relating its argument to explicit parameter `j`
    /// (`k~(x~A -> B, contains j x)`). Termination reads it as a promise to
    /// call `k` only with strict parts of `j` where that predicate is a
    /// membership, as its body shows (#102).
    pub elems: Vec<ElemPromise>,
    /// Implicit binders among the explicit ones (#161): see `Sig`.
    pub inner: Vec<usize>,
}

/// A parameter whose type's refinements mention later parameters (#102).
#[derive(Clone, Debug)]
pub struct Late {
    /// Its binder (implicit ones counted).
    pub binder: usize,
    /// Its refined type, over all the binders (not the result).
    pub ty: Tm,
    /// The later binders the refinements mention.
    pub deps: Vec<usize>,
    /// The number of binders `ty` is over.
    pub n: usize,
}

/// A call of a class's function with preconditions, whose dictionary may
/// not be found yet (#225): the context, the call, and where it is.
pub struct PendingPre {
    pub cx: Cx,
    pub call: Tm,
    pub span: Span,
    pub owner: Option<DefId>,
    pub in_spec: usize,
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
    /// The component of the body's tuple, with several cowns, and whether
    /// it is the last (then the rest of the tuple, D174).
    pub proj: Option<(usize, bool)>,
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
    /// For `ckc index` (D161): every module of the package is indexed.
    pub index_all: Option<HashSet<String>>,
    /// Different for every elaborator a process makes (keys caches, D153).
    pub uid: u64,
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
    /// Each module's imports, by name (for D143's keys).
    pub module_deps: HashMap<String, Vec<String>>,
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
    /// Branches to ask about (D144 d).
    pub probes: Vec<Probe>,
    /// The module checked, whose exported `main` is the program's (D31).
    pub root: Option<String>,
    /// References between declarations, for unused code (D144).
    pub refs: Vec<unused::Ref>,
    /// Values whose every field is observed: formatted, or compared with
    /// `==` (their type, solved later), for unused fields (D144).
    pub observed: Vec<(String, Span, Val)>,
    /// Elaborating a template's tag (#126: `format` there is no call).
    pub in_tag: bool,
    /// The context an instance needed and didn't find, while a dictionary
    /// was looked for: the class, the types, and the instance as written.
    pub ctx_missing: Option<(TyId, Vec<Val>, String)>,
    /// Calls of a template's tag outside a template (#126), by module and
    /// span: the help a type error there gets.
    pub tag_calls: HashMap<(String, u32, u32), String>,
    /// Each program module's declarations, for unused code (D144).
    pub decl_table: HashMap<String, Vec<unused::Entry>>,
    /// Declarations found unused: their branches aren't asked about.
    pub dead: Vec<(String, Span)>,
    pub specs: HashMap<DefId, Spec>,
    /// Functions exported `transparent`: reflected into importers' queries (D12).
    pub transparent: HashSet<DefId>,
    /// Constructor invariants, over the type's parameters then the fields.
    pub con_invs: HashMap<ConId, Vec<Pred>>,
    /// A type's conditions on its parameters, over the parameters (#136):
    /// obligations where the type is applied, facts in its fields.
    pub ty_conds: HashMap<TyId, Vec<Pred>>,
    /// While a signature's types are elaborated, the type applications whose
    /// conditions are checked once all its preconditions are known (#136).
    pub ty_cond_defer: Option<Vec<(Span, TyId, Vec<Val>)>>,
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
    /// The type parameters each function needs described (#170): the
    /// function its requirement comes from, and the parameter's name there.
    pub desc_reqs: HashMap<DefId, BTreeMap<usize, EqReq>>,
    /// This module's uses of generic functions, resolved after its bodies.
    pub insts: Vec<Inst>,
    /// Each dictionary built from an instance in compiled code, as a use of
    /// the function building it with the instance's types (#170).
    pub dict_insts: Vec<Inst>,
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
    /// Calls between functions of this module with no measure, which may
    /// recurse: for guessing a measure (D150).
    pub rec_calls: Vec<termination::RecCall>,
    /// For each function, `Seq.size` of what its sequence patterns take
    /// apart (§9.8): a term at a level, and its text; measures to guess.
    pub seq_sizes: HashMap<DefId, Vec<(Tm, usize, String)>>,
    /// Recursive groups whose measure is guessed in the proofs phase (D150).
    pub guess_groups: Vec<termination::GuessGroup>,
    /// Their functions: terminating by a measure, as with `decreasing`.
    pub guessed: HashSet<DefId>,
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
    /// Where each named local of a function is bound, for usage messages
    /// about one that holds no resource (a one-shot closure, D171).
    pub local_spans: HashMap<(DefId, String), Span>,
    /// Where a lambda's or `let`'s variable is bound, by its name's
    /// allocation: two variables of one name are told apart (D171, D172 d). The
    /// name is kept so the address isn't reused.
    pub binder_spans: HashMap<usize, (Name, Span)>,
    /// A lambda's parameter checked against a function type that takes it
    /// `own`: its type and the level it was bound at, so the usage check
    /// can tell, once metas are solved, whether it may be a resource (D172 b).
    pub lam_domains: HashMap<usize, (Val, usize)>,
    /// A variable whose type may be a resource but, in an arm of a `match`
    /// on a variable, is refined to one that holds none (D173): the
    /// function, the matched variable's level, the arm's constructor and
    /// the variable's level. The usage check lets it go unused there.
    pub moot_in_arm: HashSet<(DefId, usize, ConId, usize)>,
    /// The stuck `match`es whose arms `case_linear` is looking at: met again,
    /// a recursive type function adds no resource (D175).
    pub lin_visiting: std::cell::RefCell<Vec<usize>>,
    /// A `match` arm's resource names, bound as ghosts for its guard: the
    /// guard's span, for E0408.
    pub guard_vars: HashMap<(DefId, String), Span>,
    /// The function result type when elaborating a tail position (for `try`).
    pub stdlib_mode: bool,
    /// A function value checked here is applied to a strict part of the
    /// caller's parameter (#102).
    pub map_elem_sub: Option<ElemSub>,
    /// A parameter of the current function used next, as a function called
    /// only with parts of these parameters (#102).
    pub use_ctx: Option<ParamUse>,
    /// Each parameter's uses in the module's function bodies (#102).
    pub param_uses: HashMap<(DefId, usize), Vec<ParamUse>>,
    /// The module's functions whose bodies were checked (#102).
    pub body_fns: Vec<DefId>,
    /// Conditions: any of these `(callee, k, j)` promises (#102).
    pub elem_conds: Vec<Vec<ElemAlt>>,
    /// A condition made at a call: the callee's text, and the container
    /// argument's text and position, for E0301's help (#102).
    pub elem_cond_at: HashMap<u32, (String, String, usize)>,
    /// The element promises read from each checked function's body:
    /// `(k, j)` as in `Spec::elems` (#102).
    pub body_elems: HashMap<DefId, Vec<(usize, usize)>>,
    /// `(pred, c, s)`: whether `pred` is a membership, true only where its
    /// explicit argument `s` equals a strict part of argument `c` (#102);
    /// for the module being checked.
    pub memberships: HashMap<(DefId, usize, usize), bool>,
    /// Span of the `match` being compiled (for exhaustiveness errors).
    pub match_span: Span,
    /// The `match` being checked is a binding's one pattern (a `let`, a
    /// lambda's parameter, `<-`).
    pub match_binding: bool,
    /// Exhaustiveness state of the `match` being compiled.
    pub pm: pattern::PatState,
    /// Classes (D136), by their dictionary's type.
    pub class_defs: HashMap<TyId, classes::ClassDef>,
    /// A class's types (#133): `C.Name`'s definition, by class and name.
    pub assoc_defs: HashMap<(TyId, String), DefId>,
    /// An instance's dictionary reading a type from another's (#133), to
    /// find cycles.
    pub assoc_edges: Vec<(DefId, DefId)>,
    /// A class's type's predicates (#176), by the dictionary's constructor
    /// and the type's field: over the class's parameters, the dictionary,
    /// then a value of the type. Every value of the type satisfies them.
    pub class_type_preds: HashMap<(ConId, usize), Vec<Pred>>,
    /// The lemmas checking a class's type's predicates at an instance or
    /// at the class's default (#176), by name: the class's type as written
    /// (`Encoding.Unit`) and the type given (`Nat`).
    pub class_type_checks: HashMap<String, (String, String)>,
    /// While a class's type's predicates are elaborated (#176): an operator
    /// on its values there needs a class function, not a clause.
    pub in_class_type_pred: bool,
    /// Each instance member of the module being desugared, by its index:
    /// its class's name and its instance's types (#146, #145).
    pub member_heads: HashMap<usize, (String, Vec<ast::Expr>)>,
    /// Instances' functions with signatures of their own, by declaration
    /// (as `member_heads`), with the class's signature to refine (#225).
    pub inst_refines: HashMap<usize, classes::InstRefine>,
    /// Instances' functions marked `transparent`, by declaration (#249).
    pub transparent_members: HashSet<usize>,
    /// Instances' functions with signatures of their own (#225).
    pub refined_inst_fns: HashSet<DefId>,
    /// Calls of classes' functions with preconditions, to check once their
    /// dictionaries are found (#225).
    pub pending_class_pres: Vec<PendingPre>,
    /// Calls of classes' functions, and dictionaries found through a
    /// refinement alias, to check at the end of the module (#226).
    pub class_calls: Vec<PendingPre>,
    pub alias_dicts: Vec<classes::AliasDict>,
    /// Uses of classes' functions as values (#252), by their dictionary's
    /// unknown: where, and whether compared there with the function type
    /// expected, at a known instance (through a refinement alias, that
    /// comparison is their check). A local defined as one: each call of
    /// it, a call of the class's function with that dictionary.
    pub class_value_uses: Vec<(MetaId, DefId, Span, bool)>,
    pub class_local_calls: Vec<(MetaId, PendingPre)>,
    /// The instance whose member's signature is being elaborated (#146).
    pub sig_inst: Option<classes::SigInst>,
    /// Comparisons waiting for a dictionary (#133): level, expected,
    /// actual, where, the locals' names.
    pub waiting: Vec<(usize, Val, Val, Span, Vec<Name>)>,
    /// Those waiting for an instance's dictionary to be elaborated (#146).
    pub waiting_late: Vec<(usize, Val, Val, Span, Vec<Name>)>,
    /// This module's classes, until their types are registered.
    pub pending_classes: Vec<(String, Vec<String>, Vec<ast::ClassMember>, Span)>,
    /// A class function's parameters' multiplicities, by `module.Class.function`,
    /// when one is written `own` or `ghost`: its dictionary field takes an `own`
    /// one exactly once, so generic code can pass it a resource (D156 i), and a
    /// `ghost` one erased.
    pub class_mults: HashMap<String, Vec<Mult>>,
    /// Where an instance's head type stands for its class's parameter, by
    /// module and span start: an `own` there is the class's, not written.
    pub inst_heads: HashSet<(String, u32)>,
    /// Variables a field read or index of was reported for dropping part of
    /// them (E0406, E0407): the usage check says nothing more about them.
    pub part_reported: HashSet<(DefId, String)>,
    /// This module's instances, until their dictionary functions are registered.
    pub pending_insts: Vec<classes::PendingInst>,
    /// This module's types and their numbers of parameters, for instances' kinds (M25).
    pub local_ty_params: HashMap<String, usize>,
    /// This module's other names, and whether each is a type alias, for
    /// instances' heads: they are read before the module's declarations are
    /// registered.
    pub local_names: HashMap<String, bool>,
    /// Where each declaration of the module being checked came from.
    pub decl_origin: Vec<classes::Origin>,
    /// Classes' functions: their postconditions are the instances' to prove.
    pub class_methods: HashSet<DefId>,
    /// Classes' lemmas: assumed, each instance proving them.
    pub class_lemmas: HashSet<DefId>,
    /// Functions building an instance's dictionary.
    pub dict_defs: HashSet<DefId>,
    /// Instances' functions: the class's specification is theirs, so they
    /// go into their dictionary without it (D136).
    pub inst_fns: HashSet<DefId>,
    /// Each instance member's dictionary function.
    pub inst_member_of: HashMap<DefId, DefId>,
    /// Instances, by class and the head of their type.
    pub instances: HashMap<(TyId, classes::HeadKey), Vec<classes::InstInfo>>,
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
            probes: Vec::new(),
            root: None,
            refs: Vec::new(),
            observed: Vec::new(),
            in_tag: false,
            ctx_missing: None,
            tag_calls: HashMap::new(),
            decl_table: HashMap::new(),
            dead: Vec::new(),
            paths: HashMap::new(),
            index: Vec::new(),
            index_of: None,
            index_all: None,
            uid: {
                static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
                NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            },
            decl_at: HashMap::new(),
            decl_sig: HashMap::new(),
            def_class: HashMap::new(),
            checks: Vec::new(),
            check_eq_tys: HashMap::new(),
            last_eq_ty: None,
            specs: HashMap::new(),
            transparent: HashSet::new(),
            con_invs: HashMap::new(),
            ty_conds: HashMap::new(),
            ty_cond_defer: None,
            alias_preds: HashMap::new(),
            alias_subject: HashMap::new(),
            result_metas: HashMap::new(),
            arg_of: None,
            in_spec: 0,
            in_proof: 0,
            eq_reqs: HashMap::new(),
            desc_reqs: HashMap::new(),
            insts: Vec::new(),
            dict_insts: Vec::new(),
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
            rec_calls: Vec::new(),
            seq_sizes: HashMap::new(),
            guess_groups: Vec::new(),
            guessed: HashSet::new(),
            saturated_heads: HashSet::new(),
            resource_vars: HashMap::new(),
            local_spans: HashMap::new(),
            binder_spans: HashMap::new(),
            lam_domains: HashMap::new(),
            moot_in_arm: HashSet::new(),
            lin_visiting: std::cell::RefCell::new(Vec::new()),
            guard_vars: HashMap::new(),
            stdlib_mode: false,
            map_elem_sub: None,
            use_ctx: None,
            param_uses: HashMap::new(),
            body_fns: Vec::new(),
            elem_conds: Vec::new(),
            elem_cond_at: HashMap::new(),
            body_elems: HashMap::new(),
            memberships: HashMap::new(),
            match_span: Span::default(),
            match_binding: false,
            pm: Default::default(),
            class_defs: HashMap::new(),
            assoc_defs: HashMap::new(),
            assoc_edges: Vec::new(),
            member_heads: HashMap::new(),
            inst_refines: HashMap::new(),
            transparent_members: HashSet::new(),
            refined_inst_fns: HashSet::new(),
            pending_class_pres: Vec::new(),
            class_calls: Vec::new(),
            alias_dicts: Vec::new(),
            class_value_uses: Vec::new(),
            class_local_calls: Vec::new(),
            sig_inst: None,
            waiting: Vec::new(),
            waiting_late: Vec::new(),
            pending_classes: Vec::new(),
            class_type_preds: HashMap::new(),
            class_type_checks: HashMap::new(),
            in_class_type_pred: false,
            class_mults: HashMap::new(),
            inst_heads: HashSet::new(),
            part_reported: HashSet::new(),
            pending_insts: Vec::new(),
            local_ty_params: HashMap::new(),
            local_names: HashMap::new(),
            decl_origin: Vec::new(),
            class_methods: HashSet::new(),
            inst_fns: HashSet::new(),
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
            module_deps: HashMap::new(),
        }
    }

    pub fn err(&mut self, d: Diagnostic) {
        // A type error at a call of a template's tag (#126).
        let mut d = d;
        if d.code == "E0201" && d.help.is_none() {
            if let Some(h) = self.tag_calls.get(&(self.cur.clone(), d.span.start, d.span.end)) {
                d.help = Some(h.clone());
            }
        }
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

    /// A type with type functions at its head computed (`values (Last ?a)`
    /// is `?a`), stopping at an alias, whose name carries facts (`Nat`):
    /// for the types of variables a pattern or `let` binds (D176).
    pub fn reduce_type(&self, v: &Val) -> Val {
        let mut v = crate::core::force_meta(&self.g, v.clone());
        for _ in 0..64 {
            let Val::Neutral(Head::Def(d), _) = &v else { break };
            if self.alias_preds.contains_key(d) {
                break;
            }
            match crate::core::unfold(&self.g, &v) {
                Some(u) => {
                    let u = crate::core::force_meta(&self.g, u);
                    // Stuck on an unknown: keep the application, as written.
                    if matches!(&u, Val::Neutral(_, sp) if sp.iter().any(|e| matches!(e, Elim::Case(..)))) {
                        break;
                    }
                    // A class's type at a dictionary not known: as written
                    // (`Seq.Elem s`), not the dictionary's field.
                    if self.g.reads_type_field(&u) {
                        break;
                    }
                    v = u;
                }
                None => break,
            }
        }
        v
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

    /// An unknown that may depend on the type-level locals in scope (those
    /// whose type ends in `Type`), not on values.
    pub fn fresh_meta_over_types(&mut self, cx: &Cx) -> Tm {
        let m = self.g.fresh_meta();
        let mut t = Tm::Meta(m);
        for (lvl, l) in cx.locals.iter().enumerate() {
            if l.bound && self.is_type_level(&l.ty) {
                t = Tm::App(Rc::new(t), Rc::new(cx.var(lvl)), Icit::Expl, Mult::Many);
            }
        }
        t
    }

    /// Whether values of type `ty` are types or type constructors.
    fn is_type_level(&self, ty: &Val) -> bool {
        match self.force(ty) {
            Val::Univ(_) => true,
            Val::Pi(_, _, _, _, clo) => {
                let body = crate::core::apply_closure(&self.g, &clo, Val::Error);
                self.is_type_level(&body)
            }
            // Not yet known: may be a type.
            Val::Neutral(Head::Meta(_), _) => true,
            _ => false,
        }
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
        let f = head.head();
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
            // Stuck on an unknown: as written (`values s Int`), not `match s …`.
            _ => match self.force(v) {
                Val::Neutral(_, sp) if sp.iter().any(|e| matches!(e, Elim::Case(..))) => self.show_val(cx, v),
                // A class's type at a type parameter (#133): `Display.Options a`.
                Val::Neutral(_, sp) if sp.iter().any(|e| matches!(e, Elim::Field(c, i) if self.g.is_type_field(*c, *i))) => self.show_val(cx, v),
                f => self.show_val(cx, &f),
            },
        }
    }

    /// `actual`, a function type, with its parameters' `own` dropped where
    /// `expected` has none, to tell a mismatch only in `own` from others.
    fn own_as_many(&self, cx: &Cx, expected: &Val, actual: &Val) -> Option<Val> {
        fn relax(e: &Tm, a: &Tm) -> Option<Tm> {
            match (e, a) {
                (Tm::Pi(_, me, ie, _, eb), Tm::Pi(x, ma, ia, da, ab)) if ie == ia => {
                    let m = if *ma == Mult::One && *me == Mult::Many { Mult::Many } else { *ma };
                    let b = relax(eb, ab).unwrap_or_else(|| (**ab).clone());
                    Some(Tm::Pi(x.clone(), m, *ia, da.clone(), Rc::new(b)))
                }
                _ => None,
            }
        }
        let (Val::Pi(..), Val::Pi(..)) = (self.force(expected), self.force(actual)) else { return None };
        let l = cx.lvl();
        let t = relax(&quote(&self.g, l, expected), &quote(&self.g, l, actual))?;
        Some(eval(&self.g, &cx.env(), &t))
    }

    /// `own` on a function type's parameter is implied by the parameter's
    /// type (D39), decided where the arrow is written: a type still being
    /// computed there (`values s a`) may be a resource, so it is `own`. Once
    /// the type is known not to hold one (`values One Int` is `Int`), `own`
    /// means nothing: both sides drop it (D172 b).
    fn moot_own(&self, cx: &Cx, expected: &Val, actual: &Val) -> Option<(Val, Val)> {
        fn go(e: &Elab, t: &Tm, changed: &mut bool) -> Tm {
            match t {
                Tm::Pi(x, m, i, a, b) => {
                    let a2 = go(e, a, changed);
                    let b2 = go(e, b, changed);
                    let m2 = if *m == Mult::One && e.never_linear(&a2) {
                        *changed = true;
                        Mult::Many
                    } else {
                        *m
                    };
                    Tm::Pi(x.clone(), m2, *i, Rc::new(a2), Rc::new(b2))
                }
                _ => t.clone(),
            }
        }
        let (Val::Pi(..), Val::Pi(..)) = (self.force(expected), self.force(actual)) else { return None };
        let l = cx.lvl();
        let mut changed = false;
        let e = go(self, &quote(&self.g, l, expected), &mut changed);
        let a = go(self, &quote(&self.g, l, actual), &mut changed);
        changed.then(|| (eval(&self.g, &cx.env(), &e), eval(&self.g, &cx.env(), &a)))
    }

    /// A type known never to hold a resource: no variables or unsolved
    /// metas left to decide it, and not linear (D172 b).
    pub fn never_linear(&self, t: &Tm) -> bool {
        let mut fv = std::collections::BTreeSet::new();
        crate::core::free_vars(t, 0, &mut fv);
        fv.is_empty() && !has_meta(t) && !self.type_linear(t)
    }

    /// Unify, reporting a type mismatch on failure. Returns false on failure.
    pub fn unify_at(&mut self, cx: &Cx, expected: &Val, actual: &Val, span: Span, what: &str) -> bool {
        let mut r = unify(&self.g, cx.lvl(), expected, actual);
        if r.is_err() {
            if let Some((e, a)) = self.moot_own(cx, expected, actual) {
                r = unify(&self.g, cx.lvl(), &e, &a);
            }
        }
        // The types differ only in `own`: a function taking a resource where
        // the type expected doesn't say its parameter is `own` (an instance
        // of a class whose function doesn't, at a resource type, D156 i).
        if r.is_err() {
            if let Some(relaxed) = self.own_as_many(cx, expected, actual) {
                if unify(&self.g, cx.lvl(), expected, &relaxed).is_ok() {
                    let (e, a) = (self.show_written(cx, expected), self.show_written(cx, actual));
                    self.err(
                        Diagnostic::error("E0201", format!("type mismatch: expected `{e}`, found `{a}`"), span)
                            .with_label(format!("this takes a resource, but `{e}` doesn't take its parameter as `own`"))
                            .with_help("write `own` on that parameter where the type is declared (for a class's function, `x~own a` in the class)"),
                    );
                    return false;
                }
            }
        }
        if r.is_ok() {
            self.note_postponed(cx.lvl(), expected, actual, span, &cx.names());
        } else {
            self.g.postponed.borrow_mut().clear();
        }
        match r {
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
            let (h, args) = t.spine();
            match h {
                Tm::TyCon(id) => Some((*id, args.into_iter().map(|a| &**a).collect())),
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

    /// A cown owns its contents; its handle may be shared (D39), and it can't
    /// hold a resource (D156 k). A future of a resource is a resource, joined
    /// exactly once (D156 l).
    fn is_owner(&self, t: TyId) -> bool {
        Some(t) == self.g.well_known.cown
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
                    self.val_lin(&eval(&self.g, &Rc::new(Vec::new()), t), visiting)
                } else {
                    Lin::Depends
                }
            }
        }
    }

    /// A computed field type's value (an alias unfolded), with the types
    /// being visited kept, so a type holding itself through an alias
    /// (`kids~Forest`, `type Forest = x~List Tree`) is seen once.
    fn val_lin(&self, v: &Val, visiting: &mut Vec<TyId>) -> Lin {
        match self.force(v) {
            Val::TyCon(id, args) => {
                if self.is_owner(id) {
                    return Lin::No;
                }
                args.iter().fold(self.ty_lin(id, visiting), |r, a| r.or(self.val_lin(a, visiting)))
            }
            Val::TupleTy(ts) => ts.iter().fold(Lin::No, |r, a| r.or(self.val_lin(a, visiting))),
            other => Lin::of(self.val_linear(&other)),
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
                    Lin::No => args.iter().enumerate().any(|(k, a)| self.type_param(*id, k) && self.tm_linear(a, visiting)),
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

    /// A computed type: decided by evaluating it, its variables left
    /// unknown. One that can't be computed may be a resource (D112); one
    /// computed by a `match` on an unknown is one if an arm may be
    /// (`pipe_end s` may be a `File`; `values s Int` is never one, D172 e).
    fn closed_linear(&self, t: &Tm) -> bool {
        let mut fv = std::collections::BTreeSet::new();
        crate::core::free_vars(t, 0, &mut fv);
        let n = fv.iter().next_back().map_or(0, |m| m + 1);
        // Unknowns far above any context, as for fields (`field_lin`).
        let env: Vec<Val> = (0..n).map(|k| Val::var(usize::MAX / 4 + k)).collect();
        self.val_linear(&eval(&self.g, &Rc::new(env), t))
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
                    Lin::No => args.iter().enumerate().any(|(k, a)| self.type_param(id, k) && self.val_linear_at(a, depth + 1)),
                    Lin::Depends => self.fields_linear(id, &args, depth),
                }
            }
            Val::TupleTy(ts) => ts.iter().any(|a| self.val_linear_at(a, depth + 1)),
            // A type variable is generic (D45); a stuck computation of a type may be a resource.
            Val::Neutral(Head::Def(d), _) => self.def_gives_type(d),
            // A `match` stuck on an unknown: a resource if an arm may be one (D172 e).
            Val::Neutral(_, sp) if sp.iter().any(|e| matches!(e, Elim::Case(..))) => match sp.last() {
                Some(Elim::Case(c, env)) => self.case_linear(c, env, depth),
                _ => true,
            },
            Val::Neutral(..) => false,
            _ => false,
        }
    }

    /// Is parameter `k` of this type a type (`a~Type`, `f~Type -> Type`),
    /// rather than a value (`src~Bytes`)? Only a type argument can make a
    /// value a resource.
    fn type_param(&self, id: TyId, k: usize) -> bool {
        let mut t = match self.g.tys[id.0 as usize].params.get(k) {
            Some((_, t)) => t,
            None => return true,
        };
        while let Tm::Pi(_, _, _, _, b) = t {
            t = b;
        }
        matches!(t, Tm::Univ(_))
    }

    /// Might an arm of this stuck `match` be a resource type?
    fn case_linear(&self, c: &CaseTm, env: &Env, depth: usize) -> bool {
        // A recursive type function meets its own `match` again: what it
        // gives there is the same type, a resource only if a base arm is
        // (`futures ts` recurses through `futures rest`).
        let key = c as *const CaseTm as usize;
        if self.lin_visiting.borrow().contains(&key) {
            return false;
        }
        self.lin_visiting.borrow_mut().push(key);
        let r = self.case_arms_linear(c, env, depth);
        self.lin_visiting.borrow_mut().pop();
        r
    }

    fn case_arms_linear(&self, c: &CaseTm, env: &Env, depth: usize) -> bool {
        let arm = |n: usize, body: &Tm| {
            let mut e = (**env).clone();
            e.extend((0..n).map(|k| Val::var(usize::MAX / 2 + depth * 64 + k)));
            self.val_linear_at(&eval(&self.g, &Rc::new(e), body), depth + 1)
        };
        c.branches.iter().any(|(_, n, b)| arm(*n, b))
            || c.lits.iter().any(|(_, b)| arm(0, b))
            || c.default.as_ref().is_some_and(|b| arm(0, b))
    }

    pub fn type_linear(&self, t: &Tm) -> bool {
        self.tm_linear(t, &mut Vec::new())
    }

    /// Could this term (in a type position) compute a type, rather than a
    /// proposition or a value? Only an application of a definition whose
    /// result is a type, or something we can't see into (a field, a match).
    fn computes_type(&self, t: &Tm) -> bool {
        let h = t.head();
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

    /// A binder's name, recorded with where it is bound (D172 d).
    pub fn binder_name(&mut self, name: &str, span: Span) -> Name {
        let n: Name = Rc::from(name);
        self.binder_spans.insert(Rc::as_ptr(&n) as *const u8 as usize, (n.clone(), span));
        n
    }

    /// `own` on this lambda parameter is moot: its type, now known, holds
    /// no resource (D172 b).
    pub fn lam_own_moot(&self, name: &Name) -> bool {
        self.lam_domains
            .get(&(Rc::as_ptr(name) as *const u8 as usize))
            .is_some_and(|(ty, lvl)| self.never_linear(&quote(&self.g, *lvl, ty)))
    }

    /// The resource type of this lambda parameter, once known (`File`).
    pub fn lam_resource(&self, name: &Name) -> Option<String> {
        let (ty, lvl) = self.lam_domains.get(&(Rc::as_ptr(name) as *const u8 as usize))?;
        let t = quote(&self.g, *lvl, ty);
        let mut fv = std::collections::BTreeSet::new();
        crate::core::free_vars(&t, 0, &mut fv);
        (fv.is_empty() && !has_meta(&t) && self.type_linear(&t)).then(|| self.show_resource(&Cx::default(), ty))
    }

    pub fn binder_span(&self, name: &Name) -> Option<Span> {
        self.binder_spans.get(&(Rc::as_ptr(name) as *const u8 as usize)).map(|(_, s)| *s)
    }

    /// The multiplicity for a variable the program names: linear types make it `own` (D39).
    pub fn named_mult(&mut self, cx: &Cx, name: &str, ty: &Val, span: Span, declared: Mult) -> Mult {
        if let Some(f) = self.cur_fn {
            self.local_spans.insert((f, name.to_string()), span);
        }
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

    /// D45: `own` belongs on generic parameters and functions. On a linear
    /// type it is implied (W010); on a type without type variables that isn't
    /// a function it means nothing useful (E0358).
    pub fn check_own(&mut self, cx: &Cx, ty: &Tm, span: Span) {
        // A class function's `own`, at an instance's type: not written there.
        if span.start >= SYNTHETIC || self.inst_heads.contains(&(self.cur.clone(), span.start)) {
            return;
        }
        if self.type_linear(ty) {
            let tyv = self.eval(cx, ty);
            let shown = self.show_val(cx, &tyv);
            // A type still to be computed (`futures s a`) may be one.
            let mut fv = std::collections::BTreeSet::new();
            crate::core::free_vars(ty, 0, &mut fv);
            let holds = if fv.is_empty() || !self.computes_type(ty) { "holds" } else { "may hold" };
            self.err(
                Diagnostic::warning("W010", format!("`own` is implied: `{shown}` {holds} a resource"), span)
                    .with_label("this `own` can go")
                    .with_help("remove `own`; a resource is used exactly once anyway"),
            );
        } else if !matches!(ty, Tm::Pi(..)) && !self.mentions_type_var(cx, ty, 0) {
            // A function may be a closure that uses a resource, which is
            // called exactly once (D171): `f~own (Unit -> a)` takes one.
            let tyv = self.eval(cx, ty);
            let shown = self.show_val(cx, &tyv);
            self.err(
                Diagnostic::error("E0358", format!("`own` on `{shown}`, which holds no resource"), span)
                    .with_label("`own` has no use here")
                    .with_help("`own` is for generic parameters that may receive a resource, as in `v~own a`; remove it"),
            );
        }
    }

    /// Does some constructor of this type have a field that is a type?
    pub(crate) fn holds_types(&self, id: TyId) -> bool {
        // A class's dictionary holds its types (#133), but is passed and
        // found as a dictionary.
        !self.class_defs.contains_key(&id)
            && self.g.cons.iter().filter(|c| c.ty == id).any(|c| c.fields.iter().any(|f| matches!(f.3, Tm::Univ(_))))
    }

    fn mentions_type_var(&self, cx: &Cx, t: &Tm, under: usize) -> bool {
        match t {
            Tm::Var(i) if *i >= under => {
                let lvl = cx.lvl() + under - 1 - i;
                lvl < cx.locals.len()
                    && match self.force(&cx.locals[lvl].ty) {
                        Val::Univ(_) => true,
                        // A value holding types (`ts~Types`): a type computed
                        // from it is as generic as a type variable (D176).
                        Val::TyCon(id, _) => self.holds_types(id),
                        _ => false,
                    }
            }
            Tm::App(f, a, ..) => self.mentions_type_var(cx, f, under) || self.mentions_type_var(cx, a, under),
            Tm::TyConApp(_, v) | Tm::TupleTy(v) => v.iter().any(|a| self.mentions_type_var(cx, a, under)),
            Tm::Pi(_, _, _, a, b) => self.mentions_type_var(cx, a, under) || self.mentions_type_var(cx, b, under + 1),
            Tm::Meta(m) => self.g.meta(*m).is_none(),
            _ => false,
        }
    }

    /// Note that a field read or index of `t` was reported (E0406, E0407).
    pub fn part_reported_at(&mut self, cx: &Cx, t: &Tm) {
        if let (Tm::Var(ix), Some(f)) = (t, self.cur_fn) {
            if let Some(l) = cx.lvl().checked_sub(ix + 1) {
                self.part_reported.insert((f, cx.locals[l].name.to_string()));
            }
        }
    }

    /// E0404: a pattern or `_` that would drop a resource.
    pub fn report_dropped(&mut self, cx: &Cx, ty: &Val, span: Span) {
        let shown = self.show_val(cx, ty);
        self.err(
            Diagnostic::error("E0404", format!("this drops a resource of type `{shown}`"), span)
                .with_label("a resource must be used exactly once")
                .with_help(if shown.starts_with("Future ") {
                    "bind it to a name, then join it: a future of a resource is one too"
                } else {
                    "bind it to a name, then close it or pass it on"
                }),
        );
    }

    // ── obligations (§7.1) ──────────────────────────────────────────────────

    /// Record `facts in cx ⊢ goal`.
    pub fn oblige(&mut self, cx: &Cx, span: Span, kind: ObKind, text: String, goal: Val, only_if_nat: Option<Val>) {
        // In a specification only a callee's precondition is checked: a spec
        // mustn't speak of a call that can't be made (M17, D118). A
        // specification elaborated twice (a lemma's `ensures`) obliges once.
        if self.in_spec > 0 {
            if !matches!(kind, ObKind::Pre { .. } | ObKind::TypeParams { .. }) {
                return;
            }
            if self.obligations.iter().any(|o| o.span == span && o.module == self.cur && o.kind == kind) {
                return;
            }
        }
        let o = self.obligation(cx, span, kind, text, goal, only_if_nat);
        self.obligations.push(o);
    }

    /// `facts in cx ⊢ goal`, not yet recorded.
    pub fn obligation(&self, cx: &Cx, span: Span, kind: ObKind, text: String, goal: Val, only_if_nat: Option<Val>) -> Obligation {
        let ctx = (0..cx.lvl())
            .map(|l| ObLocal {
                name: cx.locals[l].name.clone(),
                ty: cx.locals[l].ty.clone(),
                refined: cx.locals[l].refined.clone(),
                def: if cx.locals[l].bound { None } else { Some(cx.env[l].clone()) },
            })
            .collect();
        let facts = cx.facts.iter().map(|(_, v)| v.clone()).collect();
        Obligation { module: self.cur.clone(), span, kind, text, ctx, facts, goal, only_if_nat, owner: self.cur_fn }
    }

    /// Whether branches here are asked about (D144 d): the program's own
    /// code, outside specifications, written by its author.
    pub fn probing(&self, span: Span) -> bool {
        self.in_spec == 0 && !self.stdlib_mode && self.completing.is_none() && span.start < SYNTHETIC && span.end > span.start
    }

    /// Ask, in the proofs phase, whether the branch entered here can run.
    pub fn probe(&mut self, cx: &Cx, span: Span, kind: ProbeKind, region: Span, before: usize) {
        if !self.probing(span) || cx.facts.is_empty() || !self.may_contradict(cx, before) {
            return;
        }
        let f = self.false_val();
        let ob = self.obligation(cx, span, ObKind::Have, String::new(), f, None);
        self.probes.push(Probe { ob, kind, region, before });
    }

    /// Whether the facts a branch adds (after the first `before`) can
    /// contradict anything: they mention a local that earlier facts, a `let`
    /// or a refined type constrain. Facts about locals nothing constrains
    /// are satisfiable, so the branch isn't asked about (most aren't).
    fn may_contradict(&self, cx: &Cx, before: usize) -> bool {
        // A fact may mention a local no longer in scope: quote high enough.
        let lvl = cx.lvl() + 1024;
        let levels = |v: &Val| {
            let mut out = Vec::new();
            free_levels(&quote(&self.g, lvl, v), lvl, 0, &mut out);
            out
        };
        let earlier: HashSet<usize> = cx.facts[..before.min(cx.facts.len())].iter().flat_map(|(_, v)| levels(v)).collect();
        let own: Vec<usize> = cx.facts[before.min(cx.facts.len())..].iter().flat_map(|(_, v)| levels(v)).collect();
        own.iter().any(|l| earlier.contains(l) || cx.locals.get(*l).is_some_and(|x| !x.bound || self.refined_ty(&x.ty)))
    }

    /// A type whose values the prover knows something about.
    fn refined_ty(&self, ty: &Val) -> bool {
        if crate::core::is_nat(&self.g, ty) {
            return true;
        }
        match self.force(ty) {
            Val::TyCon(id, args) => {
                self.g.tys[id.0 as usize].ctors.iter().any(|c| self.con_invs.get(c).is_some_and(|v| !v.is_empty()))
                    || args.iter().any(|a| self.refined_ty(a))
            }
            Val::TupleTy(ts) => ts.iter().any(|t| self.refined_ty(t)),
            Val::Neutral(Head::Var(_), _) | Val::Pi(..) | Val::Univ(_) => false,
            _ => true,
        }
    }

    /// `False`, as a value.
    pub fn false_val(&self) -> Val {
        match self.g.well_known.false_con {
            Some(c) => Val::Con(c, vec![]),
            None => Val::Error,
        }
    }

    /// The postconditions hold of `v`, a value the function returns at `at`.
    /// D121 (c): `v` is a `Nat` by construction, with no obligation: a
    /// non-negative literal, a `Nat` local, `len`, `+`, `*`, `/` or `%` of
    /// such values, or a `Nat` subtraction (which has its own obligation).
    pub fn nat_by_closure(&self, cx: &Cx, v: &Val) -> bool {
        match crate::core::force_meta(&self.g, v.clone()) {
            Val::Lit(l @ (Lit::Num(_) | Lit::Big(_))) => l.is_nonneg_int(),
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
                (Some((k, last)), _) => eval(&self.g, &Rc::new(vec![v.clone()]), &Tm::Proj(Rc::new(Tm::Var(0)), k, last)),
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
    pub fn cown_inv(&self, cx: &Cx, content: &Val, proj: Option<(usize, bool)>) -> Option<CownInv> {
        let ty = quote(&self.g, cx.lvl(), content);
        let (h, args) = ty.spine();
        let Tm::Def(d) = h else { return None };
        let preds = self.alias_preds.get(d)?.clone();
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
        let (h, args) = ty.spine();
        let Tm::Def(d) = h else { return Vec::new() };
        let Some(preds) = self.alias_preds.get(d) else { return Vec::new() };
        let prefix = Rc::new(cx.env[..at].to_vec());
        let mut env: Vec<Val> = args.iter().map(|a| eval(&self.g, &prefix, a)).collect();
        // The predicates as written, in this use's names: `n <= hi` of
        // `type Bounded lo hi = n~Int, …` is `b <= 10` for `b~Bounded 0 10`.
        let mut names = self.alias_param_names(cx, *d, &env);
        if let Some(x) = self.alias_subject.get(d) {
            names.push((x.to_string(), self.shown_operand(cx, &subject)));
        }
        env.push(subject);
        preds.iter().map(|p| (self.inst_pred(p, env.clone()), rename_words(&p.text, &names), *d)).collect()
    }

    /// An alias's parameters and how to show the arguments given them, for
    /// `rename_words`: `[("lo", "0"), ("hi", "10")]` for `Bounded 0 10`.
    pub fn alias_param_names(&self, cx: &Cx, d: DefId, args: &[Val]) -> Vec<(String, String)> {
        let mut names = Vec::new();
        let mut body = self.g.defs[d.0 as usize].body.as_ref();
        for v in args {
            let Some(Tm::Lam(x, _, _, b)) = body else { break };
            names.push((x.to_string(), self.shown_operand(cx, v)));
            body = Some(b);
        }
        names
    }

    /// A value as an operand in a predicate's text: parenthesized unless it
    /// is one word.
    fn shown_operand(&self, cx: &Cx, v: &Val) -> String {
        let t = self.show_val(cx, v);
        if t.contains(' ') && !(t.starts_with('(') && t.ends_with(')')) {
            format!("({t})")
        } else {
            t
        }
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
            Tm::PrimApp(Prim::When, _) => false,
            Tm::Pi(_, _, _, a, b) => go(a, depth) && go(b, depth + 1),
            Tm::Lam(_, _, _, b) => go(b, depth + 1),
            Tm::App(f, a, _, m) => go(f, depth) && (*m == Mult::Zero || go(a, depth)),
            Tm::Let(_, _, _, v, b) => go(v, depth) && go(b, depth + 1),
            Tm::TyConApp(_, v) | Tm::TupleTy(v) => v.iter().all(|x| go(x, depth)),
            Tm::ConApp(_, v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => v.iter().all(|x| go(x, depth)),
            Tm::Proj(x, _, _) | Tm::Field(x, _, _) => go(x, depth),
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

    /// The module of an abstract type declared in another module: its
    /// constructors and fields are private there (§6, D155).
    pub fn sealed_from(&self, t: TyId) -> Option<String> {
        let ti = &self.g.tys[t.0 as usize];
        (ti.is_abstract && *ti.module != *self.cur).then(|| ti.module.to_string())
    }

    /// E0247: a type's constructors or fields used outside its module, which
    /// exports it as abstract (D155).
    pub fn sealed_error(&self, t: TyId, what: &str, span: Span) -> Diagnostic {
        let ti = &self.g.tys[t.0 as usize];
        let m = ti.module.to_string();
        let what = match what {
            "constructors" if ti.is_record => "constructor is",
            "constructors" => "constructors are",
            _ => "fields are",
        };
        Diagnostic::error("E0247", format!("`{}` is abstract: its {what} private to module `{m}`", ti.name), span)
            .with_help(format!("use the functions module `{m}` exports for `{}`", ti.name))
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
        let (lc, rc) = (interval::constant(lt), interval::constant(rt));
        if let Val::Neutral(Head::Meta(_), _) = self.force(ty) {
            let r = self.fresh_meta_val(cx);
            self.arith_results.push(ArithResult {
                result: r.clone(),
                operands: ty.clone(),
                lvl: cx.lvl(),
                op,
                left: lc,
                right: rc,
                left_ty: lty.clone(),
                right_ty: rty.clone(),
            });
            return r;
        }
        self.arith_type(op, lc, rc, ty, lty, rty)
    }

    fn settle_arith(&mut self, a: ArithResult) {
        let t = self.arith_type(a.op, a.left, a.right, &a.operands, &a.left_ty, &a.right_ty);
        let _ = unify(&self.g, a.lvl, &a.result, &t);
    }

    pub fn solve_deferred(&mut self) {
        self.solve_instances(false);
        self.retry_waiting(false);
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
        self.retry_waiting(true);
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
                    // A class's type as written (`Seq.Elem s`), not its dictionary's field.
                    _ if self.g.reads_type_field(&t) => declared,
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
                // A class's type (#176): an operator needs its class as a clause.
                if matches!(d.kind, OpClass::Numeric | OpClass::Ordered) && self.g.reads_type_field(&t) {
                    let class = match d.what.as_str() {
                        _ if self.in_class_type_pred => None,
                        "`+`" => Some("Add"),
                        "`-`" => Some("Sub"),
                        "`*`" => Some("Mul"),
                        "`<`" | "`<=`" | "`>`" | "`>=`" => Some("Ord"),
                        _ => None,
                    };
                    let arg = if shown.contains(' ') { format!("({shown})") } else { shown.clone() };
                    diag = diag.with_help(match class {
                        Some(c) => format!(
                            "`{shown}` is a type of its own, not a number: {} on it needs the clause `{c} {arg}`, in the signature or on the class's type",
                            d.what
                        ),
                        None => format!("`{shown}` is a type of its own, not a number: reach a number through its class's functions"),
                    });
                }
                if d.what == "`+`" && matches!(&t, Val::TyCon(id, _) if Some(*id) == wk.string || Some(*id) == wk.array || Some(*id) == wk.list) {
                    diag = diag.with_help("to join strings, lists or arrays, use `++`");
                }
                self.err(diag);
            }
        }
    }

    /// The value of a number literal's text, of any size: `Int` and `Nat`
    /// have no fixed size. The lexer gives only decimal or `0x` hex digits.
    pub fn number(&self, s: &str) -> num_bigint::BigInt {
        let r = match s.strip_prefix("0x") {
            Some(h) => num_bigint::BigInt::parse_bytes(h.as_bytes(), 16),
            None => num_bigint::BigInt::parse_bytes(s.as_bytes(), 10),
        };
        r.expect("the lexer gives only digits")
    }
}

impl Default for Elab {
    fn default() -> Self {
        Self::new()
    }
}

/// Where module `name`'s program is (D53): `dir`, the directory of its file,
/// or the directory its name is relative to when `dir` ends with the name's
/// leading parts (`tools/ck`, of `ck.syntax`, is in `tools`), so that its
/// imports of the program's modules resolve when it is checked by itself.
pub fn program_root(dir: &std::path::Path, name: &str) -> std::path::PathBuf {
    let parts: Vec<&str> = name.split('.').collect();
    let leading = &parts[..parts.len().saturating_sub(1)];
    let mut root = dir.to_path_buf();
    for p in leading.iter().rev() {
        if root.file_name().is_some_and(|f| f.to_string_lossy() == *p) {
            root.pop();
        } else {
            return dir.to_path_buf();
        }
    }
    root
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
    let name = m.name.as_ref().map(|q| q.dotted()).unwrap_or_else(|| name_hint.to_string());
    e.base_dir = dir.map(|d| program_root(d, &name));
    // A standard-library file, checked by itself, is the standard library
    // (D145); it may be one of the core modules loaded next, so it is
    // indexed from the start.
    let is_std = stdlib::is_std_file(&name, std::path::Path::new(&file.name));
    e.root = Some(name.clone());
    if is_std {
        e.index_of = Some(name.clone());
    }
    // Core stdlib modules are always loaded: they define well-known types.
    for core in ["std.prelude", "std.cown", "std.future", "std.system"] {
        e.load_stdlib(core);
    }
    e.index_of = Some(name.clone());
    if is_std && e.modules.contains_key(&name) {
        return e;
    }
    e.sources.insert(name.clone(), SourceFile::new(file.name.clone(), file.text.clone()));
    e.elab_module(&name, m, is_std);
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
            // `touches` ignores variables, so any level above them all will
            // do. Not the context's length: a meta left unsolved in a header
            // is applied to every binder then in scope, the result's too,
            // which an obligation's context leaves out.
            let bad = |v: &Val| touches(&quote(g, ANY_LEVEL, v), g, &defs, &tys);
            !(bad(&o.goal)
                || o.facts.iter().any(bad)
                || o.only_if_nat.as_ref().is_some_and(bad)
                || o.ctx.iter().any(|l| bad(&l.ty) || l.def.as_ref().is_some_and(bad)))
        });
    }
}

/// A level above every variable of a value, to quote it for `touches`.
const ANY_LEVEL: usize = usize::MAX / 2;

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
        Tm::Lam(_, _, _, b) | Tm::Proj(b, _, _) => go(b),
        Tm::Field(b, c, _) => con(c) || go(b),
        Tm::Let(_, _, a, b, c) => go(a) || go(b) || go(c),
        Tm::TyConApp(ty, v) => tys.contains(ty) || v.iter().any(go),
        Tm::ConApp(c, v) => con(c) || v.iter().any(go),
        Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => v.iter().any(go),
        // A branch that is only `Error` is a case the `match` leaves out
        // (D144 e), not a type error: those are reported where they are.
        Tm::Case(s, c) => {
            let arm = |b: &Tm| !matches!(b, Tm::Error) && go(b);
            go(s)
                || c.branches.iter().any(|(k, _, b)| con(k) || arm(b))
                || c.lits.iter().any(|(_, b)| arm(b))
                || c.default.as_ref().is_some_and(arm)
        }
    }
}

/// Definitions sealed by another module (D54) that occur in `t`.
pub fn collect_sealed(t: &Tm, g: &Globals, cur: &str, out: &mut Vec<DefId>) {
    sealed_in(t, g, cur, out, &mut Vec::new());
}

/// `collect_sealed`, with the transparent instance functions whose bodies
/// were looked into (each once).
fn sealed_in(t: &Tm, g: &Globals, cur: &str, out: &mut Vec<DefId>, seen: &mut Vec<DefId>) {
    if let Tm::Def(d) = t {
        let info = &g.defs[d.0 as usize];
        if info.sealed && *info.module != *cur && !out.contains(d) {
            out.push(*d);
        }
    }
    // A class's function at a known instance is that instance's function,
    // which may be sealed (#249).
    if matches!(t, Tm::App(..)) {
        if let Some(direct) = crate::native::ir::known_instance(g, t) {
            if let (Tm::Def(f), _) = direct.spine() {
                let info = &g.defs[f.0 as usize];
                if info.sealed && *info.module != *cur && !out.contains(f) {
                    out.push(*f);
                } else if !info.sealed && *info.module != *cur {
                    // A `transparent` one's body: what it calls of its
                    // module may be sealed (#246).
                    if let (Some(b), false) = (&info.body, seen.contains(f)) {
                        seen.push(*f);
                        sealed_in(b, g, cur, out, seen);
                    }
                }
            }
        }
    }
    t.each_sub(|x, _| sealed_in(x, g, cur, out, seen));
}

/// The levels of the locals `t` mentions (for termination, D150).
pub(super) fn free_levels_pub(t: &Tm, lvl: usize, depth: usize, out: &mut Vec<usize>) {
    free_levels(t, lvl, depth, out)
}

/// The levels of the locals `t` mentions; `t` is under `depth` binders of
/// its own, at level `lvl`.
fn free_levels(t: &Tm, lvl: usize, depth: usize, out: &mut Vec<usize>) {
    match t {
        Tm::Var(i) => {
            if *i >= depth && *i - depth < lvl {
                out.push(lvl - 1 - (*i - depth));
            }
        }
        _ => t.each_sub(|x, n| free_levels(x, lvl, depth + n, out)),
    }
}

/// `text` with each whole word that `names` maps replaced: identifiers,
/// not parts of them, and nothing inside a string literal.
pub fn rename_words(text: &str, names: &[(String, String)]) -> String {
    let mut out = String::new();
    let mut word = String::new();
    let mut in_str = false;
    let flush = |word: &mut String, out: &mut String| {
        if !word.is_empty() {
            match names.iter().rev().find(|(n, _)| n == word) {
                Some((_, r)) => out.push_str(r),
                None => out.push_str(word),
            }
            word.clear();
        }
    };
    let mut prev = ' ';
    for c in text.chars() {
        if in_str {
            out.push(c);
            if c == '"' && prev != '\\' {
                in_str = false;
            }
        } else if c.is_alphanumeric() || c == '_' || (c == '.' && !word.is_empty()) {
            word.push(c);
        } else {
            flush(&mut word, &mut out);
            if c == '"' {
                in_str = true;
            }
            out.push(c);
        }
        prev = c;
    }
    flush(&mut word, &mut out);
    out
}

/// Does a term mention a metavariable?
pub(crate) fn has_meta(t: &Tm) -> bool {
    matches!(t, Tm::Meta(_)) || t.any_sub(|x, _| has_meta(x))
}
