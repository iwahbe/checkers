//! Elaboration: surface AST → core terms, with type checking (M1).
//!
//! Bidirectional checking with implicit arguments solved by pattern
//! unification. `match` is compiled to case trees with exhaustiveness
//! checking (#498). Predicates in constraints are type-checked as `Bool` and
//! recorded for the prover (M3).

mod classes;
mod cowns;
mod effects;
pub mod complete;
mod decls;
mod expr;
mod descr;
mod eq;
mod interval;
pub use interval::CODEGEN_WORK;
pub mod index;
pub(crate) mod order;
mod pattern;
mod qualify;
pub use pattern::BINDING_HELP;
mod reach;
mod refine;
pub mod settle;
mod template;
mod tyeq;
pub mod stdlib;
pub mod termination;
pub mod unused;

use crate::core::*;
use crate::diag::Diagnostic;
use crate::source::{SourceFile, Span};
use crate::syntax::ast;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;
use crate::pvec::PVec;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sym {
    Def(DefId),
    Ty(TyId),
    Con(ConId),
    /// The overloaded built-in `len` (#528)
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
    /// The term that defined it, over the locals before it: a `let`'s, or
    /// the part of a value a pattern takes. None for a bound local and for
    /// one defined by a value alone.
    pub def: Option<Rc<Tm>>,
    /// What it is known to be at compile time, once asked
    /// (`Elab::known_local`).
    pub known: std::cell::OnceCell<Option<Rc<Tm>>>,
    /// The bound locals its value refers to, by level, outermost first,
    /// once asked (`Elab::local_refers`).
    pub refers: std::cell::OnceCell<Rc<[usize]>>,
}

#[derive(Clone, Default)]
pub struct Cx {
    /// The locals' values. Each part of a context is persistent, so a copy
    /// shares it: a context kept for later, as a constraint left until the
    /// module's bodies are checked keeps the one it was made in, costs
    /// nothing to keep however many locals are in scope.
    pub env: Env,
    pub locals: PVec<Local>,
    /// The levels of the λ-bound locals (`Local::bound`), in order: what an
    /// unknown abstracts over, and where a dictionary in scope is, without
    /// a walk over every local.
    bound: PVec<usize>,
    /// The locals' names, kept apart so that a constraint left for later
    /// keeps them without a copy (`names`).
    names: Names,
    /// Elaborating a type position (after `~`): `Uname`s prefer the type namespace (#521).
    pub type_pos: bool,
    /// Facts in scope (§7.1): `Bool` values known to be true, tagged with the
    /// context length when they were added, in order.
    pub facts: PVec<(usize, Val)>,
    /// The levels of the locals of each name, outermost first, so that a
    /// name is looked up in scope (`lookup`, `Scope::count`) in time
    /// logarithmic in the number of names, not linear in the locals.
    named: crate::pmap::PMap<Name, PVec<usize>>,
}

impl Scope for Cx {
    fn len(&self) -> usize {
        self.locals.len()
    }
    fn name(&self, level: usize) -> &Name {
        &self.locals[level].name
    }
    fn at(&self, level: usize) -> Option<u32> {
        self.locals[level].span.map(|s| s.start)
    }
    fn count(&self, x: &str) -> usize {
        self.named.get(x).map_or(0, |ls| ls.len())
    }
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
    /// The locals' names, outermost first.
    pub fn names(&self) -> Names {
        self.names.clone()
    }
    pub fn bind(&mut self, name: &str, ty: Val, mult: Mult) -> usize {
        let l = self.lvl();
        self.env.push(Val::var(l));
        self.bound.push(l);
        self.name_more(name, l);
        self.names.push(Rc::from(name));
        self.locals.push(Local { name: Rc::from(name), ty, mult, bound: true, param: None, sub: None, sub_cond: None, comptime: false, span: None, refined: None, def: None, known: Default::default(), refers: Default::default() });
        l
    }
    pub fn define(&mut self, name: &str, ty: Val, val: Val, mult: Mult) -> usize {
        let l = self.lvl();
        self.env.push(val);
        self.name_more(name, l);
        self.names.push(Rc::from(name));
        self.locals.push(Local { name: Rc::from(name), ty, mult, bound: false, param: None, sub: None, sub_cond: None, comptime: false, span: None, refined: None, def: None, known: Default::default(), refers: Default::default() });
        l
    }
    /// `define`, by term `def` (over the locals before it) whose value is `val`.
    pub fn define_by(&mut self, name: &str, ty: Val, val: Val, mult: Mult, def: Tm) -> usize {
        let l = self.define(name, ty, val, mult);
        self.locals[l].def = Some(Rc::new(def));
        l
    }
    pub fn pop(&mut self) {
        let n = self.lvl().saturating_sub(1);
        self.truncate(n);
    }
    /// The local at `level` is named `name`.
    fn name_more(&mut self, name: &str, level: usize) {
        let mut ls = self.named.get(name).cloned().unwrap_or_default();
        ls.push(level);
        self.named.insert(Rc::from(name), ls);
    }
    pub fn truncate(&mut self, n: usize) {
        for l in n..self.lvl() {
            let name = self.locals[l].name.clone();
            let mut ls = self.named.get(&*name).cloned().unwrap_or_default();
            ls.pop();
            if ls.is_empty() {
                self.named.remove(&*name);
            } else {
                self.named.insert(name, ls);
            }
        }
        self.env.truncate(n);
        self.names.truncate(n);
        self.locals.truncate(n);
        while self.bound.last().is_some_and(|l| *l >= n) {
            self.bound.pop();
        }
        // In order of the levels they were added at.
        while self.facts.last().is_some_and(|(l, _)| *l > n) {
            self.facts.pop();
        }
    }
    pub fn assume(&mut self, fact: Val) {
        self.facts.push((self.locals.len(), fact));
    }
    /// The level of the innermost local named `name`.
    pub fn lookup(&self, name: &str) -> Option<usize> {
        self.named.get(name).and_then(|ls| ls.last().copied())
    }
    pub fn var(&self, lvl: usize) -> Tm {
        Tm::Var(self.lvl() - lvl - 1)
    }
    /// The levels of the λ-bound locals, outermost first.
    pub fn bound(&self) -> impl DoubleEndedIterator<Item = usize> + '_ {
        self.bound.iter().copied()
    }
}

/// A constraint on an operator's operand type, checked after the declaration (#528).
#[derive(Clone)]
pub struct Deferred {
    pub ty: Val,
    pub kind: OpClass,
    pub span: Span,
    pub what: String,
    pub lvl: usize,
    pub names: Names,
    /// The function whose body this is in.
    pub owner: Option<DefId>,
    /// The type equations that hold there (#209).
    pub givens: Vec<tyeq::Given>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum OpClass {
    Numeric,
    Ordered,
    Concat,
    HasLen,
    /// `==`/`!=` in compiled code: no functions (#614).
    Comparable,
}

/// A use of a generic function in compiled code: its type parameters'
/// arguments, for #614 (b).
#[derive(Clone)]
pub struct Inst {
    pub caller: Option<DefId>,
    pub callee: DefId,
    /// The arguments of the callee's leading implicit binders, by position.
    pub args: Vec<Val>,
    pub lvl: usize,
    pub names: Names,
    pub span: Span,
}

/// Why a function's type parameter must not be a function type (#614 b):
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
    /// A value checked against a refinement alias from a type argument (#554).
    Refined { alias: String, value: String },
    /// A refinement replaced by another in a type (#575, #579): for any value
    /// of `sub`, the predicates of `sup` hold.
    Weaken { role: WeakenRole, value: String, sub: String, sup: String, callee: Option<String> },
    /// A `when`'s cowns differ (§8.5): two of them as written. `held`: the
    /// first's binder, where both are written the same. `caller`: the
    /// function, where both are its parameters. `unlike`: their types, as
    /// shown, where they differ here but may be equal (`Cown a`, `Cown
    /// Nat`): `!=` can't compare them.
    DistinctCowns { first: String, second: String, held: Option<String>, caller: Option<String>, unlike: Option<(String, String)> },
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
    /// class's declaration of the function, as written. `at`: a refinement
    /// inside a parameter's (`pre`) or the result's type: its name, its
    /// type in the instance, and in the class.
    Refines { class: String, member: String, pre: bool, declared: String, at: Option<(String, String, String)> },
    /// A class used at a refinement alias runs the instance of the type the
    /// alias stands for (#226): a value of the class's type that instance
    /// gives must be of the alias. The class, the alias and its type, the
    /// class's function; where the use is a call, its text, else the
    /// function's parameter the instance may give values of the type to
    /// (`param`), or neither: a result, at any arguments. `inside`: a
    /// value inside the result (`Some`'s), not the result itself.
    /// `whole`: a part of the result checked as one (under a recursive
    /// type, or a function): its type at the alias and at the base.
    /// `inst`: the instance that runs, at its types (`Conv Bool Int`).
    AtAlias { class: String, inst: String, alias: String, base: String, member: String, call: Option<String>, param: Option<AliasParam>, inside: bool, whole: Option<(String, String)> },
    /// A call of a class's function at a known instance whose function
    /// requires less than the class's: a refinement of the class's result
    /// type (the alias, the result itself or a value `inside` it), which
    /// the class promises only where its preconditions (`pres`, as
    /// written) hold. The call, the instance (`Pos Box`), the function.
    KnownResult { call: String, alias: String, inside: bool, pres: String, inst: String, member: String },
    Auto,
    Have,
    /// A case a `match` leaves out can't occur there (#633 e): its pattern.
    /// `binding`: the pattern of a `let`, a lambda's parameter or `<-`,
    /// not a `match`.
    Uncovered { case: String, binding: bool },
}

/// Conditions asked whether they can all hold (E0457): a declaration's
/// preconditions, a type's conditions on its parameters, a constructor's
/// invariants, an alias's predicates. `ob` proves `false` from them, an
/// error when it is proved.
#[derive(Clone)]
pub struct Vacuity {
    pub ob: Obligation,
    pub kind: VacuityKind,
    /// The declaration's name, and where it is written.
    pub name: String,
    pub at: Span,
    /// Each fact of `ob` that is one of the conditions, as written.
    pub conds: Vec<Option<String>>,
    /// A constructor's type, by its name's span: not reported when the
    /// type's conditions are.
    pub within: Option<Span>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum VacuityKind {
    /// A function's or lemma's preconditions; its explicit parameters.
    Pre { params: Vec<String>, lemma: bool },
    TypeParams,
    Fields,
    /// A type alias's predicates on the name it binds.
    Alias { subject: String },
    /// The predicates on a class's type (`type Unit : u~Unit, u < 256`).
    ClassType { subject: String },
}

/// Where a branch was entered, asked whether it can be reached (#633 d).
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

/// Where a refinement is weakened (#575, #579).
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
    /// The type equations in scope (#209): each type with a representative,
    /// and it. The prover sees every such type as its representative.
    pub reps: Vec<(Val, Val)>,
}

/// A predicate from a header, constructor or alias, as a term over its binders.
/// Arithmetic whose operands' type wasn't known yet (#616): its
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
    /// Each operand's own type (#616).
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
    /// Its type equations (#209), over the binders, and the binders' names.
    pub teqs: Vec<tyeq::TyEq>,
    pub binder_names: Vec<Name>,
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
/// `typed`: its type is its known instance's result type already
/// (`instance_call_type`).
pub struct PendingPre {
    pub cx: Cx,
    pub call: Tm,
    pub span: Span,
    pub owner: Option<DefId>,
    pub in_spec: usize,
    pub typed: bool,
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
    /// it is the last (then the rest of the tuple, #673).
    pub proj: Option<(usize, bool)>,
}

/// An `admit` (§7.4): a fact assumed without a proof.
#[derive(Clone, Debug)]
pub struct Admit {
    pub module: String,
    pub span: Span,
    pub what: String,
}

/// Where elaboration's records ended (`Elab::mark`).
pub struct Mark {
    lens: [usize; 21],
}

/// Each module's key (`verify::module_keys`), by module name.
pub type ModuleKeys = std::rc::Rc<HashMap<String, String>>;

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
    /// For `ckc index` (#648): every module of the package is indexed.
    pub index_all: Option<HashSet<String>>,
    /// Different for every elaborator a process makes (keys caches, #638).
    pub uid: u64,
    /// Where each global is declared: module and the span of its name.
    pub decl_at: HashMap<index::Target, (String, Span)>,
    /// A declaration's header as written, for hover.
    pub decl_sig: HashMap<index::Target, String>,
    /// `function`, `lemma`, `constant` or `type` (an alias).
    pub def_class: HashMap<DefId, &'static str>,
    pub diags: Vec<(String, Diagnostic)>,
    /// Each module's declarations: span and what they declare (#599).
    pub decl_spans: HashMap<String, Vec<(Span, Option<Sym>)>>,
    seen: HashSet<(String, u32, u32, String)>,
    pub cur: String,
    loading: Vec<String>,
    /// Where `import a.b` looks for `a/b.ck` (#548).
    pub base_dir: Option<std::path::PathBuf>,
    /// Imported program modules (not the standard library), dependencies first.
    pub user_modules: Vec<String>,
    /// Each module's imports, by name (for #628's keys).
    pub module_deps: HashMap<String, Vec<String>>,
    /// The modules of the instances each module's checking chose, other
    /// than its own (#628's keys, #272): an instance is found wherever its
    /// module is loaded, so it may be in a module not imported.
    pub instance_deps: HashMap<String, std::collections::BTreeSet<String>>,
    /// The package of each module of a dependency (#608); others are the
    /// program's own package, or `std`.
    pub module_pkg: HashMap<String, String>,
    pub deferred: Vec<Deferred>,
    /// Results of arithmetic whose operands' type wasn't known yet:
    /// the result's type (a meta), the operands' type, the level.
    pub arith_results: Vec<ArithResult>,
    /// The anonymous refinement made for each range (#616).
    pub ranges: HashMap<(Option<i128>, Option<i128>), DefId>,
    /// Inferred `if`s and `match`es whose branches' ranges join (#616).
    pub joins: HashMap<MetaId, interval::Join>,
    /// The type `check` inferred for what it checked, if it did.
    pub last_checked: Option<Val>,
    /// An arithmetic operation's operands' own types (#616).
    pub operand_types: Option<(Val, Val)>,
    pub fn_meta: HashMap<DefId, FnMeta>,
    pub cur_fn: Option<DefId>,
    pub calls: Vec<CallRec>,
    /// Definitions whose bodies are being elaborated in this module (termination groups).
    pub module_fns: Vec<DefId>,
    pub obligations: Vec<Obligation>,
    /// Branches to ask about (#633 d).
    pub probes: Vec<Probe>,
    pub vacuities: Vec<Vacuity>,
    /// The declaration the next `signature` is for, to ask whether its
    /// preconditions can hold (E0457).
    pub sig_vacuity: Option<(VacuityKind, String, Span)>,
    /// The module checked, whose exported `main` is the program's (#517).
    pub root: Option<String>,
    /// References between declarations, for unused code (#633).
    pub refs: Vec<unused::Ref>,
    /// Values whose every field is observed: formatted, or compared with
    /// `==` (their type, solved later), for unused fields (#633).
    pub observed: Vec<(String, Span, Val)>,
    /// Elaborating a template's tag (#126: `format` there is no call).
    pub in_tag: bool,
    /// The context an instance needed and didn't find, while a dictionary
    /// was looked for: the class, the types, and the instance as written.
    pub ctx_missing: Option<(TyId, Vec<Val>, String)>,
    /// Calls of a template's tag outside a template (#126), by module and
    /// span: the help a type error there gets.
    pub tag_calls: HashMap<(String, u32, u32), String>,
    /// Each program module's declarations, for unused code (#633).
    pub decl_table: HashMap<String, Vec<unused::Entry>>,
    /// Declarations found unused: their branches aren't asked about.
    pub dead: Vec<(String, Span)>,
    pub specs: HashMap<DefId, Spec>,
    /// Functions exported `transparent`: reflected into importers' queries (#506).
    pub transparent: HashSet<DefId>,
    /// Constructor invariants, over the type's parameters then the fields.
    pub con_invs: HashMap<ConId, Vec<Pred>>,
    /// Constructors' type equations (#209), over the type's parameters then
    /// the fields.
    pub con_teqs: HashMap<ConId, Vec<tyeq::TyEq>>,
    /// The type equations that hold where elaboration is (#209).
    pub givens: Vec<tyeq::Given>,
    /// Type equations uses must meet, waiting for their types (#209).
    pub wanted: Vec<tyeq::Wanted>,
    /// A type's conditions on its parameters, over the parameters (#136):
    /// obligations where the type is applied, facts in its fields.
    pub ty_conds: HashMap<TyId, Vec<Pred>>,
    /// Types' type equations on their parameters (#209), over them: a
    /// condition on the type.
    pub ty_teqs: HashMap<TyId, Vec<tyeq::TyEq>>,
    /// A type's parameters' typings after the first (`n~Int, n~Nat`), with
    /// the span of each, until their refinements join its conditions.
    pub ty_param_typings: HashMap<TyId, Vec<(usize, Tm, usize, Span)>>,
    /// While a signature's types are elaborated, the type applications whose
    /// conditions are checked once all its preconditions are known (#136).
    pub ty_cond_defer: Option<Vec<(Span, TyId, Vec<Val>)>>,
    /// Refinement aliases' predicates, over the alias's parameters then its binder.
    pub alias_preds: HashMap<DefId, Vec<Pred>>,
    /// Functions' bounds from their signatures, for `Globals::bounds` once
    /// the program is proved.
    pub bounds: HashMap<DefId, Vec<Option<crate::range::Range>>>,
    /// Values known at compile time, by term (`known_value`).
    pub known_cache: std::cell::RefCell<HashMap<String, Option<Tm>>>,
    /// Definitions found to run at compile time (`runnable`).
    pub runnable_defs: std::cell::RefCell<HashSet<DefId>>,
    /// What was proved before the proofs phase, so that a module's own
    /// functions can run (§8.9, `settle`).
    pub early: std::cell::RefCell<settle::Early>,
    /// Each module's proofs once made (`verify::proved`): an imported
    /// module's functions run at compile time only once it is proved
    /// (§8.9).
    pub module_proofs: std::cell::RefCell<HashMap<String, crate::verify::Verified>>,
    /// Modules' keys (`verify::module_keys`), with how many modules were
    /// loaded when they were computed.
    pub module_keys: std::cell::RefCell<Option<(usize, ModuleKeys)>>,
    /// The modules being proved now: their functions don't run yet.
    pub proving: std::cell::RefCell<HashSet<String>>,
    /// Terms the prover's translator left out because their parts' sorts
    /// don't fit their places (§7.3): each is a type error reported, so a
    /// program without one has none.
    pub ill_sorted: std::cell::Cell<usize>,
    /// The name a refinement alias binds (`n` in `type Big = n~Int, …`).
    pub alias_subject: HashMap<DefId, Name>,
    /// The result type of a function whose result type isn't written.
    pub result_metas: HashMap<MetaId, DefId>,
    /// The function whose argument is being checked, for messages (#579).
    pub arg_of: Option<String>,
    /// Inside a type or specification: no obligations (§7.1).
    pub in_spec: usize,
    /// Inside a lemma's proof, which is never compiled (#614).
    pub in_proof: usize,
    /// Inside an argument to a `ghost` parameter, or a type bound `ghost`:
    /// erased, so a `ghost` variable used there isn't used at run time.
    pub in_erased: usize,
    /// Where each `ghost` local of a function is used outside a type, a
    /// specification, a proof or an erased argument, in order: the use a
    /// usage error (E0403) points at.
    pub ghost_uses: HashMap<(DefId, String), Vec<Span>>,
    /// Type parameters compared with `==` in compiled code, by function and
    /// binder position (#614 b).
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
    /// refined type only as a value (#579).
    pub in_app_head: bool,
    /// Postconditions to check where the current function returns (§7.1).
    pub post_target: Option<PostTarget>,
    /// The goal of the proof being elaborated (#547).
    pub proof_goal: Option<(Val, String)>,
    pub admits: Vec<Admit>,
    /// An application checked against a type with a refinement inside: its
    /// result type is unified with this before its arguments are checked (#554).
    pub app_expected: Option<Val>,
    /// The argument being checked is for a parameter or field declared with a
    /// refinement alias, so the call's own obligations cover it (#554).
    pub alias_covered: bool,
    /// The head of the application being elaborated checks its arguments'
    /// refinement aliases (a function with a spec or a constructor with invariants).
    pub head_checks_aliases: bool,
    /// The type an expression checked by inference was found to have.
    pub last_inferred: Option<Val>,
    /// Measure obligations of calls (caller, callee); kept only for calls
    /// inside one recursive group once termination is analysed.
    pub measure_obs: Vec<(DefId, DefId, Obligation)>,
    /// Calls between functions of this module with no measure, which may
    /// recurse: for guessing a measure (#641).
    pub rec_calls: Vec<termination::RecCall>,
    /// For each function, `Seq.size` of what its sequence patterns take
    /// apart (§9.8): a term at a level, and its text; measures to guess.
    pub seq_sizes: HashMap<DefId, Vec<(Tm, usize, String)>>,
    /// Recursive groups whose measure is guessed in the proofs phase (#641).
    pub guess_groups: Vec<termination::GuessGroup>,
    /// Their functions: terminating by a measure, as with `decreasing`.
    pub guessed: HashSet<DefId>,
    /// Functions recursing by `decreasing` that end without their
    /// preconditions, found while proving.
    pub ends_everywhere: std::sync::Mutex<HashSet<DefId>>,
    /// Heads of saturated calls (recursion through a partial application
    /// can't have its measure checked, E0303).
    pub saturated_heads: HashSet<Span>,
    /// `check` declarations: module, span, elaborated `Bool` term (#532).
    pub checks: Vec<(String, Span, Tm)>,
    /// For a `check` that is an `==`: the type of its sides, so a false one
    /// can show them as values of that type (a `Char` as `c'a'`).
    pub check_eq_tys: HashMap<Span, Tm>,
    /// The operand type of the `==` elaborated last (for `check_eq_tys`).
    pub last_eq_ty: Option<Val>,
    /// Variables that are linear because of their type (#533): (function, name) → (span, type).
    pub resource_vars: HashMap<(DefId, String), (Span, String)>,
    /// Where each named local of a function is bound, for usage messages
    /// about one that holds no resource (a one-shot closure, #658).
    pub local_spans: HashMap<(DefId, String), Span>,
    /// Where a lambda's or `let`'s variable is bound, by its name's
    /// allocation: two variables of one name are told apart (#658, #672 d). The
    /// name is kept so the address isn't reused.
    pub binder_spans: HashMap<usize, (Name, Span)>,
    /// A lambda's parameter checked against a function type that takes it
    /// `own`: its type and the level it was bound at, so the usage check
    /// can tell, once metas are solved, whether it may be a resource (#672 b).
    pub lam_domains: HashMap<usize, (Val, usize)>,
    /// A variable whose type may be a resource but, in an arm of a `match`
    /// on a variable, is refined to one that holds none (#664): the
    /// function, the matched variable's level, the arm's constructor and
    /// the variable's level. The usage check lets it go unused there.
    /// Ordered, so that an arm's variables are found without going through
    /// every variable in scope.
    pub moot_in_arm: BTreeSet<(DefId, usize, ConId, usize)>,
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
    pub memberships: std::cell::RefCell<HashMap<(DefId, usize, usize), bool>>,
    /// Span of the `match` being compiled (for exhaustiveness errors).
    pub match_span: Span,
    /// The `match` being checked is a binding's one pattern (a `let`, a
    /// lambda's parameter, `<-`).
    pub match_binding: bool,
    /// Exhaustiveness state of the `match` being compiled.
    pub pm: pattern::PatState,
    /// Classes (#615), by their dictionary's type.
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
    /// Those of a class's type with base types (#360), by lemma: the base
    /// types at the instance, the value's name, and whether it is the base
    /// types' own check.
    pub class_type_bases_at: HashMap<String, (Vec<ast::Expr>, String, bool)>,
    /// While a class's type's predicates are elaborated (#176): an operator
    /// on its values there needs a class function, not a clause.
    /// Elaborating a predicate on a class's type (#176): the `help:` for
    /// an operator on its values, which needs a base type (#360).
    pub in_class_type_pred: Option<String>,
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
    /// `when`s naming two or more cowns, obliged once the module's bodies
    /// are checked (§8.5).
    pub pending_distinct: Vec<cowns::PendingDistinct>,
    /// Calls with effects numbered so far (`Prim::Effect`, §7.1).
    pub effect_count: u32,
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
    /// In the signature of an instance's function or dictionary: it (for
    /// messages: a missing clause goes in the instance's context).
    pub instance_sig: Option<DefId>,
    /// Each instance's dictionary's implied clauses (#385), the types of
    /// its implicit parameters after its context's: found as its context is.
    pub inst_implied: HashMap<DefId, Vec<Tm>>,
    /// Comparisons waiting for a dictionary (#133): level, expected,
    /// actual, where, the locals' names.
    pub waiting: Vec<(usize, Val, Val, Span, Names, bool)>,
    /// Those waiting for an instance's dictionary to be elaborated (#146).
    pub waiting_late: Vec<(usize, Val, Val, Span, Names, bool)>,
    /// This module's classes, until their types are registered.
    pub pending_classes: Vec<(String, Vec<String>, Vec<ast::ClassMember>, Span)>,
    /// A class function's parameters' multiplicities, by `module.Class.function`,
    /// when one is written `own` or `ghost`: its dictionary field takes an `own`
    /// one exactly once, so generic code can pass it a resource (#643 i), and a
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
    /// go into their dictionary without it (#615).
    pub inst_fns: HashSet<DefId>,
    /// Each instance member's dictionary function.
    pub inst_member_of: HashMap<DefId, DefId>,
    /// Instances, by class and the head of their type.
    pub instances: HashMap<(TyId, classes::HeadKey), Vec<classes::InstInfo>>,
    /// Dictionaries to find once types are known.
    pub inst_reqs: Vec<classes::InstReq>,
    /// While a signature's implied clauses are looked for (#385): each
    /// dictionary a type's header asks for where the type is written.
    pub type_dict_reqs: Option<Vec<classes::InstReq>>,
    /// Inside a named precondition: `forall` is allowed (#632).
    pub forall_ok: usize,
    /// The named preconditions of the function being checked (#632).
    pub cur_hyps: Vec<(String, Val)>,
    /// The span of the name being elaborated (for a dictionary's errors).
    pub name_span: Span,
    /// Text for spans standing for code written in another module (a class's
    /// signatures in an instance, #615): module, start, end → text.
    pub text_override: HashMap<(String, u32, u32), String>,
    /// Synthetic spans (beyond any file's text, from `SYNTHETIC`), each
    /// standing for the real span it is shown at: module, start → anchor.
    pub synthetic: HashMap<(String, u32), Span>,
    /// Unknowns in a reported type mismatch (#627 c).
    pub blamed: HashSet<MetaId>,
    /// What is known at the cursor, when completing (#626).
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
            vacuities: Vec::new(),
            sig_vacuity: None,
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
            con_teqs: HashMap::new(),
            givens: Vec::new(),
            wanted: Vec::new(),
            ty_conds: HashMap::new(),
            ty_param_typings: HashMap::new(),
            ty_cond_defer: None,
            ty_teqs: HashMap::new(),
            alias_preds: HashMap::new(),
            bounds: HashMap::new(),
            known_cache: std::cell::RefCell::new(HashMap::new()),
            runnable_defs: std::cell::RefCell::new(HashSet::new()),
            early: Default::default(),
            module_proofs: std::cell::RefCell::new(HashMap::new()),
            module_keys: std::cell::RefCell::new(None),
            ill_sorted: std::cell::Cell::new(0),
            proving: std::cell::RefCell::new(HashSet::new()),
            alias_subject: HashMap::new(),
            result_metas: HashMap::new(),
            arg_of: None,
            in_spec: 0,
            in_proof: 0,
            in_erased: 0,
            ghost_uses: HashMap::new(),
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
            moot_in_arm: BTreeSet::new(),
            guard_vars: HashMap::new(),
            stdlib_mode: false,
            map_elem_sub: None,
            use_ctx: None,
            param_uses: HashMap::new(),
            body_fns: Vec::new(),
            elem_conds: Vec::new(),
            elem_cond_at: HashMap::new(),
            body_elems: HashMap::new(),
            memberships: Default::default(),
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
            pending_distinct: Vec::new(),
            effect_count: 0,
            class_calls: Vec::new(),
            alias_dicts: Vec::new(),
            class_value_uses: Vec::new(),
            class_local_calls: Vec::new(),
            sig_inst: None,
            instance_sig: None,
            inst_implied: HashMap::new(),
            waiting: Vec::new(),
            waiting_late: Vec::new(),
            pending_classes: Vec::new(),
            class_type_preds: HashMap::new(),
            class_type_checks: HashMap::new(),
            class_type_bases_at: HashMap::new(),
            in_class_type_pred: None,
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
            type_dict_reqs: None,
            forall_ok: 0,
            cur_hyps: Vec::new(),
            name_span: Span::default(),
            text_override: HashMap::new(),
            synthetic: HashMap::new(),
            blamed: HashSet::new(),
            completion: None,
            completing: None,
            module_deps: HashMap::new(),
            instance_deps: HashMap::new(),
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

    /// A value for a diagnostic: its globals marked, to be shown as the
    /// module refers to them when the diagnostic is filed (`qualify`).
    pub fn show_val(&self, cx: &Cx, v: &Val) -> String {
        let t = quote(&self.g, cx.lvl(), v);
        show_marked(&self.g, cx, &t)
    }

    pub fn eval(&self, cx: &Cx, t: &Tm) -> Val {
        eval(&self.g, &cx.env(), t)
    }

    pub fn force(&self, v: &Val) -> Val {
        let f = force(&self.g, v.clone());
        // A type with a representative in the type equations in scope
        // (#209) is seen as it.
        match self.rep_of(&f) {
            Some(r) => force(&self.g, r),
            None => f,
        }
    }

    /// A type with type functions at its head computed (`values (Last ?a)`
    /// is `?a`), stopping at an alias, whose name carries facts (`Nat`):
    /// for the types of variables a pattern or `let` binds (#662).
    pub fn reduce_type(&self, v: &Val) -> Val {
        let mut v = crate::core::force_meta(&self.g, v.clone());
        // However many: unfolding ends (see `core::unfold`).
        loop {
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
    /// Where elaboration's records end now, to drop what a trial
    /// elaboration adds (`rollback`).
    pub fn mark(&self) -> Mark {
        Mark {
            lens: [
                self.index.len(),
                self.diags.len(),
                self.deferred.len(),
                self.arith_results.len(),
                self.calls.len(),
                self.obligations.len(),
                self.probes.len(),
                self.vacuities.len(),
                self.refs.len(),
                self.observed.len(),
                self.wanted.len(),
                self.insts.len(),
                self.dict_insts.len(),
                self.elem_conds.len(),
                self.pending_class_pres.len(),
                self.class_calls.len(),
                self.alias_dicts.len(),
                self.class_value_uses.len(),
                self.class_local_calls.len(),
                self.ty_cond_defer.as_ref().map_or(0, |d| d.len()),
                self.g.postponed.borrow().len(),
            ],
        }
    }

    /// Drop what was recorded since `m`: a trial elaboration leaves no
    /// diagnostics, obligations or requests behind. (The unknowns it solved
    /// stay solved: elaborating the same text again solves them the same way.)
    pub fn rollback(&mut self, m: &Mark) {
        let [index, diags, deferred, arith, calls, obligations, probes, vacuities, refs, observed, wanted, insts, dict_insts, elem_conds, class_pres, class_calls, alias_dicts, value_uses, local_calls, ty_cond, postponed] = m.lens;
        self.index.truncate(index);
        self.diags.truncate(diags);
        self.deferred.truncate(deferred);
        self.arith_results.truncate(arith);
        self.calls.truncate(calls);
        self.obligations.truncate(obligations);
        self.probes.truncate(probes);
        self.vacuities.truncate(vacuities);
        self.refs.truncate(refs);
        self.observed.truncate(observed);
        self.wanted.truncate(wanted);
        self.insts.truncate(insts);
        self.dict_insts.truncate(dict_insts);
        self.elem_conds.truncate(elem_conds);
        self.pending_class_pres.truncate(class_pres);
        self.class_calls.truncate(class_calls);
        self.alias_dicts.truncate(alias_dicts);
        self.class_value_uses.truncate(value_uses);
        self.class_local_calls.truncate(local_calls);
        if let Some(d) = &mut self.ty_cond_defer {
            d.truncate(ty_cond);
        }
        self.g.postponed.borrow_mut().truncate(postponed);
    }

    /// Run `f` as a trial (#385): what it records is dropped after, and the
    /// requests waiting before it are set aside while it runs, so it neither
    /// sees nor settles them. Its names aren't indexed.
    pub fn trial<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let m = self.mark();
        let reqs = std::mem::take(&mut self.inst_reqs);
        let waiting = std::mem::take(&mut self.waiting);
        let waiting_late = std::mem::take(&mut self.waiting_late);
        let index = (self.index_of.take(), self.index_all.take());
        // Its diagnostics are dropped, so they may be reported after.
        let seen = self.seen.clone();
        let r = f(self);
        self.rollback(&m);
        self.seen = seen;
        self.inst_reqs = reqs;
        self.waiting = waiting;
        self.waiting_late = waiting_late;
        (self.index_of, self.index_all) = index;
        r
    }

    pub fn fresh_meta(&mut self, cx: &Cx) -> Tm {
        let m = self.g.fresh_meta();
        let mut t = Tm::Meta(m);
        for lvl in cx.bound() {
            t = Tm::App(Rc::new(t), Rc::new(cx.var(lvl)), Icit::Expl, Mult::Many);
        }
        t
    }

    /// An unknown that may depend on the type-level locals in scope (those
    /// whose type ends in `Type`), not on values.
    pub fn fresh_meta_over_types(&mut self, cx: &Cx) -> Tm {
        let m = self.g.fresh_meta();
        let mut t = Tm::Meta(m);
        for lvl in cx.bound() {
            if self.is_type_level(&cx.locals[lvl].ty) {
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
    /// implicit parameter `x` of the function `head` is (#627).
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
    /// type (#533), decided where the arrow is written: a type still being
    /// computed there (`values s a`) may be a resource, so it is `own`. Once
    /// the type is known not to hold one (`values One Int` is `Int`), `own`
    /// means nothing: both sides drop it (#672 b).
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
    /// metas left to decide it, and not linear (#672 b).
    pub fn never_linear(&self, t: &Tm) -> bool {
        let mut fv = std::collections::BTreeSet::new();
        crate::core::free_vars(t, 0, &mut fv);
        fv.is_empty() && !has_meta(t) && !self.type_linear(t)
    }

    /// Unify, reporting a type mismatch on failure. Returns false on failure.
    pub fn unify_at(&mut self, cx: &Cx, expected: &Val, actual: &Val, span: Span, what: &str) -> bool {
        let mut r = unify(&self.g, cx.lvl(), expected, actual);
        // Modulo the type equations in scope (#209).
        if r.is_err() && !self.givens.is_empty() {
            let (e, a) = (self.rep_deep(cx.lvl(), expected), self.rep_deep(cx.lvl(), actual));
            r = unify(&self.g, cx.lvl(), &e, &a);
        }
        if r.is_err() {
            if let Some((e, a)) = self.moot_own(cx, expected, actual) {
                r = unify(&self.g, cx.lvl(), &e, &a);
            }
        }
        // The types differ only in `own`: a function taking a resource where
        // the type expected doesn't say its parameter is `own` (an instance
        // of a class whose function doesn't, at a resource type, #643 i).
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
            self.note_postponed(cx.lvl(), expected, actual, span, cx.names());
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
                // follows from it (#627 c).
                let unknowns = {
                    let mut v = self.unknowns(cx.lvl(), expected);
                    for m in self.unknowns(cx.lvl(), actual) {
                        if !v.contains(&m) {
                            v.push(m);
                        }
                    }
                    v
                };
                if unknowns.iter().any(|m| self.follows_error(m)) {
                    return false;
                }
                self.blamed.extend(unknowns.iter().copied());
                let mut d = Diagnostic::error("E0201", format!("type mismatch: expected `{e}`, found `{a}`"), span)
                    .with_label(format!("{what} has type `{a}`"));
                if let Some(n) = self.unknowns_note(&unknowns, why, &e, &a) {
                    d = d.with_note(n);
                }
                // A sealed function in a type never unfolds outside its module (#537).
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
    /// An unknown that is unknown because of an error already reported: one
    /// in a reported mismatch, a dictionary not found (#627 c), or one
    /// compared with an error (an argument that failed to check).
    pub fn follows_error(&self, m: &MetaId) -> bool {
        self.blamed.contains(m) || (self.g.errored.borrow().contains(m) && self.reported_error())
    }

    /// An error has been reported: an error in a term is one of its.
    pub fn reported_error(&self) -> bool {
        self.diags.iter().any(|(_, d)| d.severity == crate::diag::Severity::Error)
    }

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

    /// What the named unknowns in a message stand for (#627): "`?f` is
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

/// What `val_linear` is inside: a type whose field's type is computed, or
/// a stuck `match` (by its address), innermost first.
#[derive(Clone, Copy, PartialEq)]
enum LinStep {
    Ty(TyId),
    Case(usize),
}

struct LinPath {
    step: LinStep,
    up: Option<Rc<LinPath>>,
}

impl LinPath {
    fn has(p: &Option<Rc<LinPath>>, step: LinStep) -> bool {
        let mut p = p.as_deref();
        while let Some(q) = p {
            if q.step == step {
                return true;
            }
            p = q.up.as_deref();
        }
        false
    }
}

impl Elab {
    /// A primitive resource (#533): implemented by the runtime as an open, stateful thing.
    fn is_primitive_resource(&self, t: TyId) -> bool {
        let ti = &self.g.tys[t.0 as usize];
        matches!((&*ti.module, &*ti.name), ("std.files", "File") | ("std.proc", "Child"))
    }

    /// A cown owns its contents; its handle may be shared (#533), and it can't
    /// hold a resource (#643 k). A future of a resource is a resource, joined
    /// exactly once (#643 l).
    fn is_owner(&self, t: TyId) -> bool {
        Some(t) == self.g.well_known.cown
    }

    /// Is a type declared with a resource in a constructor field (#533)? `Depends`
    /// when a field's type is computed from the parameters (`pipe_end ss.stdout`,
    /// #611): then it is a resource for some arguments and not others.
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
            // A type variable: a generic container (#545), decided by its argument.
            Tm::Var(_) | Tm::Pi(..) | Tm::Univ(_) | Tm::Lit(_) | Tm::Error => Lin::No,
            // A proposition (a refinement field) or a value: never a resource.
            _ if !self.computes_type(t) => Lin::No,
            // Computed: an alias, an application, a match.
            _ => {
                let mut fv = std::collections::BTreeSet::new();
                crate::core::free_vars(t, 0, &mut fv);
                if fv.is_empty() {
                    self.val_lin(&eval(&self.g, &crate::core::Env::new(), t), visiting)
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
    /// unknown. One that can't be computed may be a resource (#611); one
    /// computed by a `match` on an unknown is one if an arm may be
    /// (`pipe_end s` may be a `File`; `values s Int` is never one, #672 e).
    fn closed_linear(&self, t: &Tm) -> bool {
        let mut fv = std::collections::BTreeSet::new();
        crate::core::free_vars(t, 0, &mut fv);
        let n = fv.iter().next_back().map_or(0, |m| m + 1);
        // Unknowns far above any context, as for fields (`field_lin`).
        let env: Vec<Val> = (0..n).map(|k| Val::var(usize::MAX / 4 + k)).collect();
        self.val_linear(&eval(&self.g, &crate::core::Env::from(env), t))
    }

    /// Is a value of this type linear (#533)? However deep the type: a
    /// worklist. A type holding itself at the same arguments is seen once;
    /// one whose field's type is computed (`Lin::Depends`) and that holds
    /// itself at other arguments holds types without end, and is taken as
    /// a resource.
    pub fn val_linear(&self, v: &Val) -> bool {
        // Types are compared quoted at a level above every variable in
        // them, the fresh ones included.
        const KEY: usize = usize::MAX - (1 << 24);
        let fresh = std::cell::Cell::new(usize::MAX / 2);
        let fresh = || {
            let l = fresh.get();
            fresh.set(l + 1);
            Val::var(l)
        };
        let mut seen: Vec<(TyId, Vec<Tm>)> = Vec::new();
        let mut work: Vec<(Val, Option<Rc<LinPath>>)> = vec![(v.clone(), None)];
        while let Some((v, path)) = work.pop() {
            match self.force(&v) {
                Val::TyCon(id, args) => {
                    if self.is_owner(id) {
                        continue;
                    }
                    match self.ty_lin(id, &mut Vec::new()) {
                        Lin::Yes => return true,
                        Lin::No => work.extend(args.iter().enumerate().filter(|(k, _)| self.type_param(id, *k)).map(|(_, a)| (a.clone(), path.clone()))),
                        Lin::Depends => {
                            let key: Vec<Tm> = args.iter().map(|a| quote(&self.g, KEY, a)).collect();
                            if seen.iter().any(|(i, k)| *i == id && k.len() == key.len() && k.iter().zip(&key).all(|(a, b)| tm_eq(a, b))) {
                                continue;
                            }
                            if LinPath::has(&path, LinStep::Ty(id)) {
                                return true;
                            }
                            seen.push((id, key));
                            let inner = Some(Rc::new(LinPath { step: LinStep::Ty(id), up: path }));
                            // The fields of `id` at these arguments.
                            for c in &self.g.tys[id.0 as usize].ctors {
                                let mut env: Vec<Val> = args.to_vec();
                                for f in self.g.cons[c.0 as usize].fields.iter() {
                                    if f.1 != Mult::Zero && self.field_lin(&f.3, &mut Vec::new()) != Lin::No {
                                        work.push((eval(&self.g, &crate::core::Env::from(env.clone()), &f.3), inner.clone()));
                                    }
                                    // Earlier fields are unknown here: fresh variables far above any context.
                                    env.push(fresh());
                                }
                            }
                        }
                    }
                }
                Val::TupleTy(ts) => work.extend(ts.iter().map(|a| (a.clone(), path.clone()))),
                // A type variable is generic (#545); a stuck computation of a type may be a resource.
                Val::Neutral(Head::Def(d), _) => {
                    if self.def_gives_type(d) {
                        return true;
                    }
                }
                // A `match` stuck on an unknown: a resource if an arm may be one (#672 e).
                Val::Neutral(_, sp) if sp.iter().any(|e| matches!(e, Elim::Case(..))) => match sp.last() {
                    Some(Elim::Case(c, env)) => {
                        // A recursive type function meets its own `match`
                        // again: what it gives there is the same type, a
                        // resource only if a base arm is (`futures ts`
                        // recurses through `futures rest`).
                        let key = &**c as *const CaseTm as usize;
                        if LinPath::has(&path, LinStep::Case(key)) {
                            continue;
                        }
                        let inner = Some(Rc::new(LinPath { step: LinStep::Case(key), up: path }));
                        let mut arm = |n: usize, body: &Tm| {
                            let mut e = env.clone();
                            e.extend((0..n).map(|_| fresh()));
                            work.push((eval(&self.g, &e, body), inner.clone()));
                        };
                        for (_, n, b) in c.branches.iter() {
                            arm(*n, b);
                        }
                        for (_, b) in c.lits.iter() {
                            arm(0, b);
                        }
                        if let Some(b) = c.default.as_ref() {
                            arm(0, b);
                        }
                    }
                    _ => return true,
                },
                _ => {}
            }
        }
        false
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

    /// A binder's name, recorded with where it is bound (#672 d).
    pub fn binder_name(&mut self, name: &str, span: Span) -> Name {
        let n: Name = Rc::from(name);
        self.binder_spans.insert(Rc::as_ptr(&n) as *const u8 as usize, (n.clone(), span));
        n
    }

    /// `own` on this lambda parameter is moot: its type, now known, holds
    /// no resource (#672 b).
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

    /// The multiplicity for a variable the program names: linear types make it `own` (#533).
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

    /// #545: `own` belongs on generic parameters and functions. On a linear
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
            // called exactly once (#658): `f~own (Unit -> a)` takes one.
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
                        // from it is as generic as a type variable (#662).
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
                .with_help(if crate::core::plain(&shown).starts_with("Future ") {
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
        // mustn't speak of a call that can't be made (M17). A
        // specification elaborated twice (a lemma's `ensures`) obliges once;
        // each of several conditions at one place is its own obligation.
        if self.in_spec > 0 {
            if !matches!(kind, ObKind::Pre { .. } | ObKind::TypeParams { .. }) {
                return;
            }
            if self.obligations.iter().any(|o| o.span == span && o.module == self.cur && o.kind == kind && o.text == text) {
                return;
            }
        }
        let o = self.obligation(cx, span, kind, text, goal, only_if_nat);
        self.obligations.push(o);
    }

    /// A call in a typing (`r~Box (grow 1 k)`) may rely on every condition
    /// of the declaration, wherever it is written, except one that depends
    /// on it (§7.1). Types are elaborated before conditions, so the
    /// obligations made since `from` get those facts here. `typings`: each
    /// typing's type, and how many locals were in scope where it was
    /// elaborated (`None` for a name that isn't the declaration's); `conds`:
    /// each condition's span, its term over `cx`, and the typing it is a
    /// refinement of, if any (else it is written on its own, and relies on
    /// the conditions before it in `conds`).
    ///
    /// The conditions whose calls need facts form a graph: a typing's calls
    /// rely on every other condition, a written condition's on those before
    /// it. A condition with calls depends on what its calls rely on, so a
    /// typing's calls may not rely on a condition with calls that reaches
    /// the typing back, directly or through other conditions.
    pub fn rely_on_conditions(&mut self, from: usize, typings: &[(Span, Option<usize>)], conds: &[(Span, Tm, Option<usize>)], cx: &Cx) {
        let total = cx.lvl();
        let nt = typings.len();
        let within = |span: Span, at: Span| at.start <= span.start && span.end <= at.end;
        // Regions: the typings, then the written conditions.
        let region = |c: usize| conds[c].2.unwrap_or(nt + c);
        let mut obligations: Vec<Vec<usize>> = vec![Vec::new(); nt + conds.len()];
        for i in from..self.obligations.len() {
            let o = &self.obligations[i];
            if o.module != self.cur {
                continue;
            }
            let at = typings.iter().position(|(ty, _)| within(o.span, *ty)).or_else(|| {
                (0..conds.len()).find(|&c| conds[c].2.is_none() && within(o.span, conds[c].0)).map(|c| nt + c)
            });
            if let Some(r) = at {
                obligations[r].push(i);
            }
        }
        // The conditions each region's calls rely on.
        let uses = |r: usize| -> Vec<usize> {
            if r < nt {
                (0..conds.len()).filter(|&c| region(c) != r).collect()
            } else {
                (0..r - nt).collect()
            }
        };
        let edges: Vec<Vec<usize>> = (0..nt + conds.len())
            .map(|r| {
                if obligations[r].is_empty() {
                    return Vec::new();
                }
                let mut out: Vec<usize> = uses(r).into_iter().map(region).filter(|&q| !obligations[q].is_empty()).collect();
                out.sort_unstable();
                out.dedup();
                out
            })
            .collect();
        let reaches = |from: usize, to: usize| {
            let mut seen = vec![false; edges.len()];
            let mut stack = vec![from];
            while let Some(r) = stack.pop() {
                if r == to {
                    return true;
                }
                if !std::mem::replace(&mut seen[r], true) {
                    stack.extend(edges[r].iter().copied());
                }
            }
            false
        };
        let conds: Vec<(Val, usize, usize)> = conds
            .iter()
            .enumerate()
            .map(|(c, (_, tm, _))| {
                let mut used = Vec::new();
                free_levels(tm, total, 0, &mut used);
                (self.eval(cx, tm), used.iter().max().map_or(0, |l| l + 1), region(c))
            })
            .collect();
        for (t, (_, base)) in typings.iter().enumerate() {
            let Some(base) = *base else { continue };
            let facts: Vec<(Val, usize)> = conds
                .iter()
                .filter(|(_, needs, r)| *r != t && *needs <= base && (obligations[*r].is_empty() || !reaches(*r, t)))
                .map(|(v, needs, _)| (self.rep_deep(total, v), *needs))
                .collect();
            for &i in &obligations[t] {
                // Over the locals in scope where the typing was elaborated.
                let n = self.obligations[i].ctx.len();
                self.obligations[i].facts.extend(facts.iter().filter(|(_, needs)| *needs <= n).map(|(v, _)| v.clone()));
            }
        }
    }

    /// `facts in cx ⊢ goal`, not yet recorded.
    pub fn obligation(&self, cx: &Cx, span: Span, kind: ObKind, text: String, goal: Val, only_if_nat: Option<Val>) -> Obligation {
        let ctx = (0..cx.lvl())
            .map(|l| ObLocal {
                name: cx.locals[l].name.clone(),
                // With the type equations' representatives (#209): the
                // prover never sees an equation.
                ty: self.rep_deep(l, &cx.locals[l].ty),
                refined: cx.locals[l].refined.as_ref().map(|r| self.rep_deep(cx.lvl(), r)),
                def: if cx.locals[l].bound { None } else { Some(self.rep_deep(l, &cx.env[l])) },
            })
            .collect();
        let facts = cx.facts.iter().map(|(_, v)| self.rep_deep(cx.lvl(), v)).collect();
        let goal = self.rep_deep(cx.lvl(), &goal);
        Obligation { module: self.cur.clone(), span, kind, text, ctx, facts, goal, only_if_nat, owner: self.cur_fn, reps: self.rep_pairs() }
    }

    /// Whether branches here are asked about (#633 d): the program's own
    /// code, outside specifications, written by its author.
    pub fn probing(&self, span: Span) -> bool {
        self.in_spec == 0 && !self.stdlib_mode && self.completing.is_none() && span.start < SYNTHETIC && span.end > span.start
    }

    /// Ask, in the proofs phase, whether the conditions in `cx`'s facts can
    /// all hold (E0457). `conds`: the text of each fact that is one of the
    /// declaration's conditions, by its index; nothing is asked without one.
    pub fn ask_vacuity(&mut self, cx: &Cx, kind: VacuityKind, name: &str, at: Span, conds: Vec<Option<String>>, within: Option<Span>) {
        if conds.iter().all(|c| c.is_none()) || self.completing.is_some() {
            return;
        }
        let f = self.false_val();
        let ob = self.obligation(cx, at, ObKind::Have, String::new(), f, None);
        self.vacuities.push(Vacuity { ob, kind, name: name.to_string(), at, conds, within });
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
        let earlier: HashSet<usize> = cx.facts.iter().take(before).flat_map(|(_, v)| levels(v)).collect();
        let own: Vec<usize> = cx.facts.iter().skip(before).flat_map(|(_, v)| levels(v)).collect();
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
            Some(c) => Val::Con(c, vec![].into()),
            None => Val::Error,
        }
    }

    /// The postconditions hold of `v`, a value the function returns at `at`.
    /// #609 (c): `v` is a `Nat` by construction, with no obligation: a
    /// non-negative integer known at compile time (§8.9: a literal, a named
    /// constant, `math.pow 2 3`), a `Nat` local, `len`, `+`, `*`, `/` or `%`
    /// of such values, or a `Nat` subtraction (which has its own obligation).
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
                            let mut e = env.clone();
                            e.extend(std::iter::repeat_n(Val::Error, n));
                            self.nat_by_closure(cx, &eval(&self.g, &e, body))
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
                        if free.is_empty() && crate::core::is_nat(&self.g, &eval(&self.g, &crate::core::Env::from(vec![Val::Error; np + i]), fty)) {
                            return true;
                        }
                    }
                }
                // A call of a function (global or local) whose result type is `Nat`.
                let call = match &v {
                    // Not a class's function with preconditions: at a known
                    // instance whose function requires less, the call meets
                    // only that function's, and the class promises a `Nat`
                    // only where its own hold (the prover knows so much).
                    Val::Neutral(Head::Def(d), _) if self.class_methods.contains(d) && self.specs.get(d).is_some_and(|s| s.preds.iter().any(|p| !p.is_post)) => false,
                    Val::Neutral(Head::Def(d), sp) => {
                        let ty = eval(&self.g, &crate::core::Env::new(), &self.g.defs[d.0 as usize].ty);
                        self.returns_nat(&ty, sp)
                    }
                    Val::Neutral(Head::Var(l), sp) => cx.locals.get(*l).is_some_and(|x| self.returns_nat(&x.ty, sp)),
                    _ => false,
                };
                // Or what a `Nat` local stands for (`j` in `Some (n, j)`, a
                // `let` of a `match`), or a value known at compile time.
                call || {
                    let t = quote(&self.g, cx.lvl(), &v);
                    cx.locals.iter().zip(cx.env.iter()).any(|(x, e)| {
                        crate::core::is_nat(&self.g, &x.ty) && crate::core::tm_eq(&quote(&self.g, cx.lvl(), e), &t)
                    })
                } || self.known_in(cx, &v).is_some_and(|l| l.is_nonneg_int())
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
    /// construction (#609 c) needs no obligation.
    pub fn nat_pred_holds(&self, cx: &Cx, p: &Pred, v: &Val) -> bool {
        matches!(p.alias, Some((_, d)) if Some(d) == self.g.well_known.nat) && self.nat_by_closure(cx, v)
    }

    pub fn oblige_posts_at(&mut self, cx: &Cx, v: Val, at: Span) {
        self.oblige_posts_typed(cx, v, at, None)
    }

    /// The same, knowing the returned value's type: one already a `Nat`
    /// meets a `Nat` result (#609).
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
                (Some((k, last)), _) => eval(&self.g, &crate::core::Env::from(vec![v.clone()]), &Tm::Proj(Rc::new(Tm::Var(0)), k, last)),
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
        Val::Neutral(Head::Prim(p, args.into()), Rc::new(Vec::new()))
    }

    pub fn bool_val(&self, b: bool) -> Val {
        let c = if b { self.g.well_known.true_con } else { self.g.well_known.false_con };
        match c {
            Some(c) => Val::Con(c, Rc::new([])),
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
        self.sources.get(&self.cur).map(|f| source_text(&f.text, span, false)).unwrap_or_default()
    }

    /// An expression's text, as `src_text`, keeping a block's lines (a
    /// `match` across several): what is shown of a predicate.
    pub fn expr_text(&self, e: &crate::syntax::ast::Expr) -> String {
        if let Some(t) = self.text_override.get(&(self.cur.clone(), e.span.start, e.span.end)) {
            return t.clone();
        }
        self.sources.get(&self.cur).map(|f| source_text(&f.text, e.span, has_block(e))).unwrap_or_default()
    }

    /// If `ty`, a type term over the first `at` locals of `cx`, is a refinement
    /// alias (`U8`), its predicates about `subject` (#500, §7.1).
    pub fn alias_facts(&self, cx: &Cx, at: usize, ty: &Tm, subject: Val) -> Vec<(Val, String, DefId)> {
        let (h, args) = ty.spine();
        let Tm::Def(d) = h else { return Vec::new() };
        let Some(preds) = self.alias_preds.get(d) else { return Vec::new() };
        let prefix = cx.env.prefix(at);
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
        eval(&self.g, &crate::core::Env::from(env), &p.tm)
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
                !(info.opaque && info.body.is_some()) && !self.g.run_time_only.borrow().contains(d)
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
            Some(t) => Val::TyCon(t, args.into()),
            None => Val::Error,
        }
    }

    /// `Nat`, the prelude's refinement of `Int` (#609).
    pub fn nat(&self) -> Val {
        match self.g.well_known.nat {
            Some(d) => eval(&self.g, &crate::core::Env::new(), &Tm::Def(d)),
            None => self.int(),
        }
    }
    /// The prelude's `Char` (a refinement of `Nat`), the type of `c'…'` (#509).
    pub fn char_ty(&self) -> Val {
        self.prelude_alias("Char")
    }
    /// The prelude's `U8`, the type of `'x'` (#509).
    pub fn u8_ty(&self) -> Val {
        self.prelude_alias("U8")
    }
    fn prelude_alias(&self, name: &str) -> Val {
        let d = self.g.defs.iter().position(|i| i.module.as_ref() == "std.prelude" && i.name.as_ref() == name);
        match d {
            Some(d) => eval(&self.g, &crate::core::Env::new(), &Tm::Def(DefId(d as u32))),
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
    /// `Bytes`, the alias of `Array U8` (#624).
    pub fn bytes(&self) -> Val {
        match self.g.well_known.bytes {
            Some(d) => eval(&self.g, &crate::core::Env::new(), &Tm::Def(d)),
            None => Val::Error,
        }
    }
    pub fn array_of(&self, elem: Val) -> Val {
        self.ty_val(self.g.well_known.array, vec![elem])
    }
    pub fn unit(&self) -> Val {
        Val::TupleTy(vec![].into())
    }

    /// The module of an abstract type declared in another module: its
    /// constructors and fields are private there (§6, #637).
    pub fn sealed_from(&self, t: TyId) -> Option<String> {
        let ti = &self.g.tys[t.0 as usize];
        (ti.is_abstract && *ti.module != *self.cur).then(|| ti.module.to_string())
    }

    /// E0247: a type's constructors or fields used outside its module, which
    /// exports it as abstract (#637).
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
        // The result of arithmetic: settle its operands' type first.
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

    /// The type of `+ - * / %` on operands of type `ty`: `Nat` for
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
    /// isn't known yet, once it is (#616).
    #[allow(clippy::too_many_arguments)]
    pub fn arith_result(&mut self, cx: &Cx, op: Prim, lt: &Tm, rt: &Tm, ty: &Val, lty: &Val, rty: &Val) -> Val {
        let (lc, rc) = (self.known_int(cx, lt), self.known_int(cx, rt));
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
        self.solve_wanted(false);
        self.solve_instances(false);
        self.retry_waiting(false);
        self.solve_wanted(false);
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
        self.retry_waiting(true);
        self.solve_wanted(true);
        let mut failed: Vec<(Span, String, Diagnostic)> = Vec::new();
        for d in ds {
            if d.kind == OpClass::Comparable {
                self.solve_comparable(&d);
                continue;
            }
            // Seen through the type equations where the operator is (#209).
            let saved = std::mem::replace(&mut self.givens, d.givens.clone());
            let t = self.force(&d.ty);
            self.givens = saved;
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
                let shown = crate::core::show_marked(&self.g, &d.names.to_vec(), &shown_tm);
                let need = match d.kind {
                    OpClass::Numeric => "numbers (`Nat` or `Int`)",
                    OpClass::Ordered => "numbers (`Nat` or `Int`) to compare",
                    OpClass::Concat => "a `String`, `List` or `Array`",
                    OpClass::HasLen => "a `String`, `List` or `Array`",
                    OpClass::Comparable => unreachable!(),
                };
                // A number where a class's type with a base type is expected
                // (#360): its values are numbers, but not every number.
                if let (Some(base), true) = (crate::core::class_type_base(&self.g, &t), d.what == "a number literal") {
                    let b = crate::core::show_marked(&self.g, &d.names.to_vec(), &quote(&self.g, d.lvl, &base));
                    failed.push((
                        d.span,
                        shown.clone(),
                        Diagnostic::error("E0201", format!("type mismatch: expected `{shown}`, found a number"), d.span)
                            .with_label("this is a number")
                            .with_note(format!("`{shown}` is a type of its own: its values are `{b}`s, but numbers aren't known to be its values"))
                            .with_help(format!("use a value of `{shown}`, such as one the class's functions give")),
                    ));
                    continue;
                }
                let mut diag = Diagnostic::error("E0210", format!("{} needs {need}, but this is `{shown}`", d.what), d.span)
                    .with_label(format!("has type `{shown}`"));
                // A class's type (#176): an operator needs its class as a clause.
                if matches!(d.kind, OpClass::Numeric | OpClass::Ordered) && self.g.reads_type_field(&t) {
                    let class = match d.what.as_str() {
                        _ if self.in_class_type_pred.is_some() => None,
                        "`+`" => Some("Add"),
                        "`-`" => Some("Sub"),
                        "`*`" => Some("Mul"),
                        "`<`" | "`<=`" | "`>`" | "`>=`" => Some("Ord"),
                        _ => None,
                    };
                    let arg = if shown.contains(' ') { format!("({shown})") } else { shown.clone() };
                    diag = diag.with_help(match (class, &self.in_class_type_pred) {
                        (_, Some(help)) => help.clone(),
                        (Some(c), None) => format!(
                            "`{shown}` is a type of its own, not a number: {} on it needs the clause `{c} {arg}`, in the signature or on the class's type",
                            d.what
                        ),
                        (None, None) => format!("`{shown}` is a type of its own, not a number: reach a number through its class's functions"),
                    });
                }
                if d.what == "`+`" && matches!(&t, Val::TyCon(id, _) if Some(*id) == wk.string || Some(*id) == wk.array || Some(*id) == wk.list) {
                    diag = diag.with_help("to join strings, lists or arrays, use `++`");
                }
                failed.push((d.span, shown, diag));
            }
        }
        // An operand of an operator that failed on the same type fails for
        // the same reason (`256` of `u < 256`): reported once, at the operator.
        for (k, (span, shown, diag)) in failed.iter().enumerate() {
            let within = failed.iter().enumerate().any(|(j, (s2, sh2, _))| {
                j != k && sh2 == shown && s2.start <= span.start && span.end <= s2.end && (s2.start, s2.end) != (span.start, span.end)
            });
            if !within {
                self.err(diag.clone());
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

/// Where module `name`'s program is (#548): `dir`, the directory of its file,
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

/// `check_module`; completing at byte `at` (#626), only the body there is
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
    // (#629); it may be one of the core modules loaded next, so it is
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
    /// Check as far as possible past errors (#599): set aside the obligations
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
        Tm::Known(k) => k.any_con(|c| con(&c)),
        Tm::Pi(_, _, _, a, b) | Tm::App(a, b, ..) => go(a) || go(b),
        Tm::Lam(_, _, _, b) | Tm::Proj(b, _, _) => go(b),
        Tm::Field(b, c, _) => con(c) || go(b),
        Tm::Let(_, _, a, b, c) => go(a) || go(b) || go(c),
        Tm::TyConApp(ty, v) => tys.contains(ty) || v.iter().any(go),
        Tm::ConApp(c, v) => con(c) || v.iter().any(go),
        Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => v.iter().any(go),
        // A branch that is only `Error` is a case the `match` leaves out
        // (#633 e), not a type error: those are reported where they are.
        Tm::Case(s, c) => {
            let arm = |b: &Tm| !matches!(b, Tm::Error) && go(b);
            go(s)
                || c.branches.iter().any(|(k, _, b)| con(k) || arm(b))
                || c.lits.iter().any(|(_, b)| arm(b))
                || c.default.as_ref().is_some_and(arm)
        }
    }
}

/// Definitions sealed by another module (#537) that occur in `t`.
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

/// The levels of the locals `t` mentions (for termination, #641).
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
/// The source text at `span`: one line with its whitespace collapsed, or,
/// with `lines`, its lines as written (less the first's indentation), when
/// it has several.
pub fn source_text(src: &str, span: Span, lines: bool) -> String {
    let Some(t) = src.get(span.start as usize..span.end as usize) else { return String::new() };
    if !lines || !t.contains('\n') {
        return t.split_whitespace().collect::<Vec<_>>().join(" ");
    }
    let line_start = src[..span.start as usize].rfind('\n').map_or(0, |i| i + 1);
    let col = src[line_start..span.start as usize].chars().count();
    let mut out: Vec<&str> = Vec::new();
    for (k, l) in t.lines().enumerate() {
        let l = l.trim_end();
        if l.trim().is_empty() {
            continue;
        }
        let lead = l.len() - l.trim_start().len();
        out.push(if k == 0 { l } else { &l[lead.min(col)..] });
    }
    out.join("\n")
}

/// Is `e` a layout block, or one of its branches: written on several lines
/// whose breaks are part of it?
pub fn has_block(e: &crate::syntax::ast::Expr) -> bool {
    use crate::syntax::ast::ExprKind;
    match &e.kind {
        ExprKind::Match(..) | ExprKind::Block(_) | ExprKind::When(_) => true,
        ExprKind::If(_, t, f) => has_block(t) || has_block(f),
        _ => false,
    }
}

/// A predicate's text for a one-line message: its first line, with `…` for
/// the rest of a block.
pub fn first_line(text: &str) -> String {
    match text.split_once('\n') {
        Some((first, _)) => format!("{first} …"),
        None => text.to_string(),
    }
}

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
