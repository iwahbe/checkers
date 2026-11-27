//! Core terms, values, normalization by evaluation, and unification (§3–§4).
//!
//! Terms use de Bruijn *indices*; values use de Bruijn *levels* and closures
//! (Kovács' elaboration-zoo design). Metavariables stand for implicit
//! arguments and unknown types; they are solved by pattern unification.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use num_bigint::BigInt;
use num_traits::{Euclid, Zero};
use std::rc::Rc;

pub type Name = Rc<str>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mult {
    Zero,
    One,
    Many,
}

impl Mult {
    pub fn times(self, o: Mult) -> Mult {
        match (self, o) {
            (Mult::Zero, _) | (_, Mult::Zero) => Mult::Zero,
            (Mult::One, x) | (x, Mult::One) => x,
            _ => Mult::Many,
        }
    }
    pub fn plus(self, o: Mult) -> Mult {
        match (self, o) {
            (Mult::Zero, x) | (x, Mult::Zero) => x,
            _ => Mult::Many,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Icit {
    Expl,
    Impl,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TyId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MetaId(pub u32);

#[derive(Clone, Debug, PartialEq)]
pub enum Lit {
    Num(i128),
    /// An integer outside `i128`'s range, never one inside it (`Lit::int`
    /// keeps that), so equal numbers are equal literals.
    Big(Rc<BigInt>),
    Str(Rc<str>),
    Bytes(Rc<[u8]>),
}

impl Lit {
    /// The literal of integer `n`: `Num` when it fits in `i128`, else `Big`.
    pub fn int(n: BigInt) -> Lit {
        match i128::try_from(&n) {
            Ok(m) => Lit::Num(m),
            Err(_) => Lit::Big(Rc::new(n)),
        }
    }

    /// The integer this literal is, if it is one.
    pub fn as_int(&self) -> Option<BigInt> {
        match self {
            Lit::Num(n) => Some(BigInt::from(*n)),
            Lit::Big(n) => Some((**n).clone()),
            _ => None,
        }
    }

    /// Whether this is an integer `>= 0`.
    pub fn is_nonneg_int(&self) -> bool {
        match self {
            Lit::Num(n) => *n >= 0,
            Lit::Big(n) => n.sign() != num_bigint::Sign::Minus,
            _ => false,
        }
    }
}

/// Built-in operations. Evaluated when their arguments are literals; stuck otherwise.
#[derive(Clone, Debug, PartialEq)]
pub enum Prim {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Neg,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Concat,
    Len,
    Index,
    /// `par t` — identity to the type checker and prover (#522).
    Par,
    When,
    /// A stdlib function implemented in Rust (`__builtin`), by qualified name.
    Builtin(Rc<str>),
    /// `forall x y : …, p` (#632): its one argument is a Π over the
    /// variables whose body is the `Bool` (premises implying the
    /// conclusion). Only in specifications; never evaluated or compiled.
    Forall,
    /// A call with effects (§7.1, §8.3), its one argument: the call itself
    /// at run time; to the prover a value of its own, this one call's,
    /// known by what the callee promises. Numbered, so two calls differ.
    Effect(u32),
}

#[derive(Clone, Debug)]
pub enum Tm {
    Var(usize),
    Def(DefId),
    TyCon(TyId),
    Con(ConId),
    Meta(MetaId),
    Univ(u32),
    Pi(Name, Mult, Icit, Rc<Tm>, Rc<Tm>),
    Lam(Name, Mult, Icit, Rc<Tm>),
    /// The `Mult` is the multiplicity of the function's parameter (for usage checking).
    App(Rc<Tm>, Rc<Tm>, Icit, Mult),
    Let(Name, Mult, Rc<Tm>, Rc<Tm>, Rc<Tm>),
    Lit(Lit),
    TupleTy(Vec<Tm>),
    Tuple(Vec<Tm>),
    /// Component `i` of a tuple. With `rest` (the last component a pattern
    /// names), the components from `i` on: `(a, b, c)` is `(a, (b, c))`, so
    /// `(x, r)` binds `r` to `(b, c)` (#673).
    Proj(Rc<Tm>, usize, bool),
    /// Record projection: field `index` (counting fields only, not type parameters).
    Field(Rc<Tm>, ConId, usize),
    TyConApp(TyId, Vec<Tm>),
    /// Saturated constructor: type parameters, then fields.
    ConApp(ConId, Vec<Tm>),
    PrimApp(Prim, Vec<Tm>),
    Case(Rc<Tm>, Rc<CaseTm>),
    /// A value known at compile time (§8.9), of any size, as a node of a
    /// graph (`known`): closed, and with no subterms of its own, so walks
    /// over terms take no stack for it.
    Known(crate::known::Value),
    /// Placeholder after an error has been reported; unifies with anything.
    Error,
}

#[derive(Debug)]
pub struct CaseTm {
    /// (constructor, number of field binders, body under those binders)
    pub branches: Vec<(ConId, usize, Tm)>,
    pub lits: Vec<(Lit, Tm)>,
    pub default: Option<Tm>,
}

impl Tm {
    /// Whether `f` holds of one of this term's immediate subterms. `f` is
    /// given each subterm, in order, with the number of binders this term
    /// puts it under, and is not asked again once it has held.
    pub fn any_sub(&self, mut f: impl FnMut(&Tm, usize) -> bool) -> bool {
        match self {
            Tm::Var(_) | Tm::Def(_) | Tm::TyCon(_) | Tm::Con(_) | Tm::Meta(_) | Tm::Univ(_) | Tm::Lit(_) | Tm::Known(_) | Tm::Error => false,
            Tm::Pi(_, _, _, a, b) => f(a, 0) || f(b, 1),
            Tm::Lam(_, _, _, b) => f(b, 1),
            Tm::App(a, b, _, _) => f(a, 0) || f(b, 0),
            Tm::Let(_, _, a, b, c) => f(a, 0) || f(b, 0) || f(c, 1),
            Tm::TupleTy(v) | Tm::Tuple(v) | Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::PrimApp(_, v) => v.iter().any(|x| f(x, 0)),
            Tm::Proj(a, _, _) | Tm::Field(a, _, _) => f(a, 0),
            Tm::Case(s, c) => {
                f(s, 0)
                    || c.branches.iter().any(|(_, n, b)| f(b, *n))
                    || c.lits.iter().any(|(_, b)| f(b, 0))
                    || c.default.as_ref().is_some_and(|b| f(b, 0))
            }
        }
    }

    /// Whether `f` holds of every immediate subterm (see `any_sub`).
    pub fn all_sub(&self, mut f: impl FnMut(&Tm, usize) -> bool) -> bool {
        !self.any_sub(|x, n| !f(x, n))
    }

    /// `f` on every immediate subterm, in order (see `any_sub`).
    pub fn each_sub(&self, mut f: impl FnMut(&Tm, usize)) {
        self.any_sub(|x, n| {
            f(x, n);
            false
        });
    }

    /// This term with each immediate subterm replaced by `f` of it (see
    /// `any_sub`); a term with no subterms is itself.
    pub fn map_sub(&self, mut f: impl FnMut(&Tm, usize) -> Tm) -> Tm {
        match self {
            Tm::Var(_) | Tm::Def(_) | Tm::TyCon(_) | Tm::Con(_) | Tm::Meta(_) | Tm::Univ(_) | Tm::Lit(_) | Tm::Known(_) | Tm::Error => self.clone(),
            Tm::Pi(x, m, i, a, b) => Tm::Pi(x.clone(), *m, *i, Rc::new(f(a, 0)), Rc::new(f(b, 1))),
            Tm::Lam(x, m, i, b) => Tm::Lam(x.clone(), *m, *i, Rc::new(f(b, 1))),
            Tm::App(a, b, i, m) => Tm::App(Rc::new(f(a, 0)), Rc::new(f(b, 0)), *i, *m),
            Tm::Let(x, m, a, b, c) => Tm::Let(x.clone(), *m, Rc::new(f(a, 0)), Rc::new(f(b, 0)), Rc::new(f(c, 1))),
            Tm::TupleTy(v) => Tm::TupleTy(v.iter().map(|x| f(x, 0)).collect()),
            Tm::Tuple(v) => Tm::Tuple(v.iter().map(|x| f(x, 0)).collect()),
            Tm::TyConApp(c, v) => Tm::TyConApp(*c, v.iter().map(|x| f(x, 0)).collect()),
            Tm::ConApp(c, v) => Tm::ConApp(*c, v.iter().map(|x| f(x, 0)).collect()),
            Tm::PrimApp(p, v) => Tm::PrimApp(p.clone(), v.iter().map(|x| f(x, 0)).collect()),
            Tm::Proj(x, i, r) => Tm::Proj(Rc::new(f(x, 0)), *i, *r),
            Tm::Field(x, c, i) => Tm::Field(Rc::new(f(x, 0)), *c, *i),
            Tm::Case(s, c) => Tm::Case(
                Rc::new(f(s, 0)),
                Rc::new(CaseTm {
                    branches: c.branches.iter().map(|(k, n, b)| (*k, *n, f(b, *n))).collect(),
                    lits: c.lits.iter().map(|(l, b)| (l.clone(), f(b, 0))).collect(),
                    default: c.default.as_ref().map(|b| f(b, 0)),
                }),
            ),
        }
    }

    /// What an application applies: `f` of `f a b`. A term that is not an
    /// application is its own head.
    pub fn head(&self) -> &Tm {
        let mut h = self;
        while let Tm::App(f, ..) = h {
            h = f;
        }
        h
    }

    /// An application's head and its arguments, in order: `f` and `[a, b]`
    /// of `f a b`.
    pub fn spine(&self) -> (&Tm, Vec<&Rc<Tm>>) {
        let mut h = self;
        let mut args = Vec::new();
        while let Tm::App(f, a, ..) = h {
            args.push(a);
            h = f;
        }
        args.reverse();
        (h, args)
    }

    /// `spine`, with the arguments as terms of their own.
    pub fn spine_cloned(&self) -> (&Tm, Vec<Tm>) {
        let (h, args) = self.spine();
        (h, args.into_iter().map(|a| (**a).clone()).collect())
    }
}

/// The values of the locals a term is evaluated under, outermost first:
/// persistent, so a closure keeps it and a value added makes a new one
/// without a copy.
pub type Env = crate::pvec::PVec<Val>;

#[derive(Clone, Debug)]
pub struct Closure {
    pub env: Env,
    pub body: Rc<Tm>,
}

#[derive(Clone, Debug)]
pub enum Head {
    Var(usize),
    Meta(MetaId),
    /// A definition that is not unfolded (`partial`, builtin, or out of fuel).
    Def(DefId),
    /// A primitive stuck on its arguments, shared like a constructor's: a
    /// value refers to it from every value built on it.
    Prim(Prim, Rc<[Val]>),
}

#[derive(Clone, Debug)]
pub enum Elim {
    App(Val, Icit),
    Proj(usize, bool),
    Field(ConId, usize),
    Case(Rc<CaseTm>, Env),
}

#[derive(Clone, Debug)]
pub enum Val {
    Neutral(Head, Rc<Vec<Elim>>),
    Lam(Name, Mult, Icit, Closure),
    Pi(Name, Mult, Icit, Rc<Val>, Closure),
    Univ(u32),
    TyCon(TyId, Rc<[Val]>),
    Con(ConId, Rc<[Val]>),
    Lit(Lit),
    TupleTy(Rc<[Val]>),
    Tuple(Rc<[Val]>),
    /// A constructor or tuple known at compile time (§8.9), taken apart one
    /// level when it is looked at (`force_meta`, `known_open`); its other
    /// nodes stay graph nodes. Literals in a graph are `Lit`s at once.
    Known(crate::known::Value),
    Error,
}

impl Val {
    pub fn var(l: usize) -> Val {
        Val::Neutral(Head::Var(l), Rc::new(Vec::new()))
    }
}

// ── global tables ────────────────────────────────────────────────────────────

pub struct DefInfo {
    pub name: Name,
    pub module: Name,
    pub ty: Tm,
    /// None for builtins and declarations whose body is not available.
    pub body: Option<Tm>,
    /// Do not unfold during evaluation (`partial`).
    pub opaque: bool,
    /// Sealed by its module (#537): does not unfold outside it.
    pub sealed: bool,
    /// Unfolds without spending fuel: a type that can't recurse (an alias,
    /// whose cycles are errors, #557, or one the compiler makes), so
    /// unfolding it always ends. A function, which may recurse, never is,
    /// whatever its result type (#711).
    pub alias: bool,
    /// Binder positions (over the whole Π-type) that are `comptime` (#541).
    /// A function with any is a compile-time function: staging inlines it.
    pub comptime: Vec<usize>,
}

pub struct TyInfo {
    pub name: Name,
    pub module: Name,
    /// Parameter names, multiplicities and types (types in the context of earlier params).
    pub params: Vec<(Name, Tm)>,
    pub ctors: Vec<ConId>,
    pub is_record: bool,
    /// Abstract to importers (or a built-in type such as `Nat`).
    pub is_abstract: bool,
    /// Per parameter: occurs only strictly positively in constructor fields
    /// (for an abstract type: marked `+`, #511).
    pub positive: Vec<bool>,
    /// Per parameter of an abstract type: marked `-`, so it occurs only
    /// negatively (#511).
    pub negative: Vec<bool>,
    /// How many of `params`, the last ones, are the dictionaries of its
    /// header's class clauses (#385): implicit arguments, found where the
    /// type is written, never shown, and erased.
    pub dicts: usize,
}

pub struct ConInfo {
    pub name: Name,
    pub ty: TyId,
    /// Position among the type's constructors.
    pub tag: usize,
    /// Fields: name, multiplicity, implicit?, type (in context params ++ earlier fields).
    pub fields: Vec<(Name, Mult, Icit, Tm)>,
}

pub enum MetaEntry {
    Unsolved,
    Solved(Val),
}

pub struct Globals {
    pub defs: Vec<DefInfo>,
    pub tys: Vec<TyInfo>,
    pub cons: Vec<ConInfo>,
    pub metas: RefCell<Vec<MetaEntry>>,
    /// The implicit parameters unknowns stand for, for messages (#627).
    pub meta_origins: RefCell<HashMap<MetaId, MetaOrigin>>,
    /// Remaining δ-unfoldings before evaluation stops unfolding (guards against
    /// non-terminating definitions whose termination isn't checked yet).
    pub fuel: Cell<u64>,
    pub well_known: WellKnown,
    /// Comparisons of a class's type at a dictionary not found yet with
    /// another type (#133): neither failed nor guessed, they wait for the
    /// dictionary (level, the two types).
    pub postponed: RefCell<Vec<(usize, Val, Val)>>,
    /// Unknowns compared with an error: what they are isn't known because
    /// of an error already reported, so what follows from them isn't
    /// reported either.
    pub errored: RefCell<std::collections::HashSet<MetaId>>,
    /// Each type's value parameters that its fields' types are computed
    /// from (#170), once worked out (`value_params_needed`).
    pub value_params: RefCell<HashMap<TyId, std::collections::BTreeSet<usize>>>,
    /// Each function's constant bounds on its binders (implicit ones too),
    /// then on its result, where its signature gives them (`x~U8`,
    /// `0 <= x`), which native code relies on (§14). Empty until the
    /// program is `proved` (`Elab::bounds` until then).
    pub bounds: HashMap<DefId, Vec<Option<crate::range::Range>>>,
    /// Constants' values known at compile time (§8.9), for code generation:
    /// set once the program is proved, as `bounds` is (`Elab::known_value`).
    /// Each is a literal, `()` or a `Tm::Known`, compiled as static data.
    pub known: RefCell<HashMap<DefId, Tm>>,
    /// The builtins never run when compiling (§8.9): those with effects
    /// (§7.1, given a capability, a `Sched`, a file or a process handle, by
    /// their signatures) and `std.hint.blackbox`, whose result is never
    /// known. Neither the type checker, staging nor folding computes a call
    /// of one.
    pub run_time_only: RefCell<std::collections::HashSet<DefId>>,
    /// Every obligation of the program is proved, and none of its facts is
    /// assumed by an `admit` (§13.3): native code compiled from here relies
    /// on the proofs, with no run-time checks of guarded operations. False
    /// in a `check` or staging, which run before proving.
    pub proved: bool,
    /// Whether native code's calls on static data are computed when
    /// compiling (§8.9), and within how much work: set where `proved` is,
    /// since then its calls meet their preconditions.
    pub fold_work: std::cell::Cell<Option<u64>>,
    /// The base types of classes' types that have one (#360), by their
    /// field of the dictionary: closed types.
    pub type_bases: HashMap<(ConId, usize), Vec<Tm>>,
    /// The longest identity environment `id_env` gave.
    ids: RefCell<Env>,
    /// Known values kept across builds (§8.9): their keys and storage.
    pub known_disk: RefCell<crate::known_cache::KnownCache>,
    /// Whether `force` keeps what it computes across builds (§8.9): the
    /// cache is on, and no kept computation is running (one kept value's
    /// parts aren't kept on their own).
    pub keeping: Cell<bool>,
    /// How many more definitions evaluation may unfold before it stops:
    /// `force_kept`'s first attempt counts its unfoldings with it.
    pub unfolds_left: Cell<u64>,
}

#[derive(Default, Clone)]
pub struct WellKnown {
    pub bool_ty: Option<TyId>,
    pub true_con: Option<ConId>,
    pub false_con: Option<ConId>,
    /// The prelude's `Nat`, a refinement alias of `Int` (#609).
    pub nat: Option<DefId>,
    pub int: Option<TyId>,
    pub string: Option<TyId>,
    /// `Bytes`, the prelude's alias of `Array U8` (#624).
    pub bytes: Option<DefId>,
    pub array: Option<TyId>,
    /// The prelude's fixed-width aliases and `Char`, with the layout of an
    /// array of them (`checkers_rt::array::Layout`, #624).
    pub layouts: Vec<(DefId, u8)>,
    pub list: Option<TyId>,
    pub nil: Option<ConId>,
    pub cons: Option<ConId>,
    pub option: Option<TyId>,
    pub some: Option<ConId>,
    pub none: Option<ConId>,
    pub result: Option<TyId>,
    pub ok: Option<ConId>,
    pub err: Option<ConId>,
    pub future: Option<TyId>,
    pub cown: Option<TyId>,
    pub sched: Option<TyId>,
    /// `std.string`'s `debug`, the derived `Debug` (#126).
    pub debug: Option<DefId>,
    /// Hand-written `instance Debug T`: the type and the instance's
    /// `debug`, which the runtime calls for `T`'s constructors (#126).
    pub debug_insts: Vec<(TyId, DefId)>,
    /// The type parameters (by position) of each function that shows
    /// values of them, itself or through functions it calls: they are
    /// passed their type's descriptor, not only its layout (#170).
    pub desc_params: HashMap<DefId, std::collections::BTreeSet<usize>>,
    /// Classes' functions, each reading a field of its dictionary, and the
    /// functions building instances' dictionaries (#615): a class's
    /// function at a known instance's dictionary is compiled as a direct
    /// call of that instance's function (§14).
    pub class_fns: std::collections::HashSet<DefId>,
    pub dict_fns: std::collections::HashSet<DefId>,
}

pub const DEFAULT_FUEL: u64 = 200_000;

impl Globals {
    /// The environment of `l` locals in which each is its own variable,
    /// for evaluating a term under them: a prefix of the longest one asked
    /// for so far, which is kept, so each costs about what the length
    /// asked grew by, not `l`.
    pub fn id_env(&self, l: usize) -> Env {
        let mut ids = self.ids.borrow_mut();
        while ids.len() < l {
            let n = ids.len();
            ids.push(Val::var(n));
        }
        ids.prefix(l)
    }

    pub fn new() -> Globals {
        Globals {
            defs: Vec::new(),
            tys: Vec::new(),
            cons: Vec::new(),
            metas: RefCell::new(Vec::new()),
            meta_origins: RefCell::new(HashMap::new()),
            fuel: Cell::new(DEFAULT_FUEL),
            well_known: WellKnown::default(),
            postponed: RefCell::new(Vec::new()),
            errored: RefCell::new(std::collections::HashSet::new()),
            value_params: RefCell::new(HashMap::new()),
            bounds: HashMap::new(),
            known: RefCell::new(HashMap::new()),
            run_time_only: RefCell::new(std::collections::HashSet::new()),
            ids: RefCell::new(Env::new()),
            proved: false,
            fold_work: std::cell::Cell::new(None),
            type_bases: HashMap::new(),
            known_disk: RefCell::new(Default::default()),
            keeping: Cell::new(crate::verify::cache_dir().is_some()),
            unfolds_left: Cell::new(u64::MAX),
        }
    }

    pub fn fresh_meta(&self) -> MetaId {
        let mut m = self.metas.borrow_mut();
        m.push(MetaEntry::Unsolved);
        MetaId(m.len() as u32 - 1)
    }

    pub fn meta(&self, m: MetaId) -> Option<Val> {
        match &self.metas.borrow()[m.0 as usize] {
            MetaEntry::Solved(v) => Some(v.clone()),
            MetaEntry::Unsolved => None,
        }
    }

    pub fn bool_val(&self, b: bool) -> Val {
        let c = if b { self.well_known.true_con } else { self.well_known.false_con };
        match c {
            Some(c) => Val::Con(c, Rc::new([])),
            None => Val::Error,
        }
    }

    /// A class's type (#133): `C.Name`, a definition `\t {d} -> d.$Name`
    /// reading a `Type` field of the dictionary. The field, if `d` is one.
    pub fn assoc_field(&self, d: DefId) -> Option<(ConId, usize)> {
        self.assoc_def(d).map(|(c, i, _)| (c, i))
    }

    /// A class's type (#133): its field, and how many type parameters the
    /// class has (`\s h {d} -> d.$Name`, #145), so it takes one more
    /// argument, the dictionary.
    pub fn assoc_def(&self, d: DefId) -> Option<(ConId, usize, usize)> {
        let mut b = self.defs.get(d.0 as usize)?.body.as_ref()?;
        let mut n = 0;
        while let Tm::Lam(_, _, Icit::Expl, x) = b {
            b = x;
            n += 1;
        }
        let Tm::Lam(_, _, Icit::Impl, b) = b else { return None };
        match &**b {
            Tm::Field(x, c, i) if n > 0 && matches!(**x, Tm::Var(0)) && self.is_type_field(*c, *i) => Some((*c, *i, n)),
            _ => None,
        }
    }

    /// Is field `i` of constructor `c` a type (of type `Type`)?
    pub fn is_type_field(&self, c: ConId, i: usize) -> bool {
        self.cons.get(c.0 as usize).and_then(|ci| ci.fields.get(i)).is_some_and(|f| matches!(f.3, Tm::Univ(_)))
    }

    /// Is `v` a class's type read from a dictionary not known (#133),
    /// `d.$Elem`? Messages show it as written instead (`Seq.Elem s`).
    pub fn reads_type_field(&self, v: &Val) -> bool {
        matches!(v, Val::Neutral(_, sp) if matches!(sp.last(), Some(Elim::Field(c, i)) if self.is_type_field(*c, *i)))
    }

    /// A class's type in its dictionary (#133): a field of multiplicity 0
    /// that is kept at run time, holding its type's word, for generic code's
    /// arrays of it and for showing it.
    pub fn is_dict_type_field(&self, c: ConId, k: usize) -> bool {
        self.is_type_field(c, k) && self.cons[c.0 as usize].fields[k].0.starts_with('$')
    }

    /// Whether field `k` of constructor `c` is kept at run time.
    pub fn is_runtime_field(&self, c: ConId, k: usize) -> bool {
        self.cons[c.0 as usize].fields[k].1 != Mult::Zero || self.is_dict_type_field(c, k)
    }

    /// A type with one constructor whose fields keep exactly one value at
    /// run time is stored as that value, with no object around it (#170):
    /// that field's position, for the type's constructor `c`.
    pub fn unboxed_field(&self, c: ConId) -> Option<usize> {
        let ci = self.cons.get(c.0 as usize)?;
        if self.tys[ci.ty.0 as usize].ctors.len() != 1 {
            return None;
        }
        let mut kept = (0..ci.fields.len()).filter(|&k| self.is_runtime_field(c, k));
        let k = kept.next()?;
        kept.next().is_none().then_some(k)
    }

    pub fn arity_ty(&self, t: TyId) -> usize {
        self.tys[t.0 as usize].params.len()
    }

    pub fn arity_con(&self, c: ConId) -> usize {
        let ci = &self.cons[c.0 as usize];
        self.arity_ty(ci.ty) + ci.fields.len()
    }
}

impl Default for Globals {
    fn default() -> Self {
        Self::new()
    }
}

// ── evaluation ───────────────────────────────────────────────────────────────

pub fn push(env: &Env, v: Val) -> Env {
    let mut e = env.clone();
    e.push(v);
    e
}

pub fn apply_closure(g: &Globals, c: &Closure, v: Val) -> Val {
    eval(g, &push(&c.env, v), &c.body)
}

/// Build the curried λ-term for an unsaturated head with `n` arguments.
fn eta(n: usize, icits: &[Icit], mk: impl Fn(Vec<Tm>) -> Tm) -> Tm {
    let args: Vec<Tm> = (0..n).map(|i| Tm::Var(n - 1 - i)).collect();
    let mut t = mk(args);
    for i in (0..n).rev() {
        t = Tm::Lam(Rc::from(format!("x{i}")), Mult::Many, icits.get(i).copied().unwrap_or(Icit::Expl), Rc::new(t));
    }
    t
}

pub fn con_icits(g: &Globals, c: ConId) -> Vec<Icit> {
    let ci = &g.cons[c.0 as usize];
    let mut v = vec![Icit::Impl; g.arity_ty(ci.ty)];
    v.extend(ci.fields.iter().map(|f| f.2));
    v
}

pub fn eval(g: &Globals, env: &Env, t: &Tm) -> Val {
    match t {
        Tm::Var(i) => env[env.len() - 1 - i].clone(),
        // Definitions are unfolded lazily, by `force` (see there).
        Tm::Def(d) => Val::Neutral(Head::Def(*d), Rc::new(Vec::new())),
        Tm::TyCon(t) => {
            let n = g.arity_ty(*t);
            if n == 0 {
                Val::TyCon(*t, Rc::new([]))
            } else {
                let tid = *t;
                eval(g, &crate::core::Env::new(), &eta(n, &[], |args| Tm::TyConApp(tid, args)))
            }
        }
        Tm::Con(c) => {
            let n = g.arity_con(*c);
            if n == 0 {
                Val::Con(*c, Rc::new([]))
            } else {
                let cid = *c;
                let icits = con_icits(g, cid);
                eval(g, &crate::core::Env::new(), &eta(n, &icits, |args| Tm::ConApp(cid, args)))
            }
        }
        Tm::Meta(m) => match g.meta(*m) {
            Some(v) => v,
            None => Val::Neutral(Head::Meta(*m), Rc::new(Vec::new())),
        },
        Tm::Univ(u) => Val::Univ(*u),
        Tm::Pi(x, m, i, a, b) => {
            Val::Pi(x.clone(), *m, *i, Rc::new(eval(g, env, a)), Closure { env: env.clone(), body: b.clone() })
        }
        Tm::Lam(x, m, i, b) => Val::Lam(x.clone(), *m, *i, Closure { env: env.clone(), body: b.clone() }),
        Tm::App(f, a, i, _) => {
            let fv = eval(g, env, f);
            let av = eval(g, env, a);
            app(g, fv, av, *i)
        }
        Tm::Let(_, _, _, v, b) => {
            let vv = eval(g, env, v);
            eval(g, &push(env, vv), b)
        }
        Tm::Lit(l) => Val::Lit(l.clone()),
        Tm::TupleTy(ts) => Val::TupleTy(ts.iter().map(|t| eval(g, env, t)).collect()),
        Tm::Tuple(ts) => Val::Tuple(ts.iter().map(|t| eval(g, env, t)).collect()),
        Tm::Proj(t, i, rest) => proj(g, eval(g, env, t), *i, *rest),
        Tm::Field(t, c, i) => field(g, eval(g, env, t), *c, *i),
        Tm::TyConApp(t, args) => Val::TyCon(*t, args.iter().map(|a| eval(g, env, a)).collect()),
        Tm::ConApp(c, args) => Val::Con(*c, args.iter().map(|a| eval(g, env, a)).collect()),
        Tm::PrimApp(p, args) => prim(g, p, args.iter().map(|a| eval(g, env, a)).collect()),
        Tm::Case(s, c) => case(g, eval(g, env, s), c.clone(), env.clone()),
        Tm::Known(k) => known_val(k),
        Tm::Error => Val::Error,
    }
}

/// The value of a known value's node: a literal at once, a constructor or
/// tuple left as `Val::Known` until it is looked at.
pub fn known_val(k: &crate::known::Value) -> Val {
    use crate::known::Node;
    match k.node() {
        Node::Con(..) | Node::Tuple(_) | Node::Array(..) | Node::Closure(_) | Node::Pap(_) => Val::Known(k.clone()),
        Node::Unit | Node::Erased => Val::Tuple(Rc::new([])),
        _ => Val::Lit(k.lit().expect("a literal node")),
    }
}

/// A known value's node taken apart one level: a constructor's fields
/// (after placeholders for its type's parameters, which a known value
/// doesn't keep) and a tuple's components are its parts, as `known_val`s.
pub fn known_open(g: &Globals, k: &crate::known::Value) -> Val {
    use crate::known::Node;
    match k.node() {
        Node::Con(c, xs) => {
            let np = g.arity_ty(g.cons[c.0 as usize].ty);
            let args: Vec<Val> = std::iter::repeat_n(Val::Univ(0), np).chain(xs.iter().map(|x| known_val(&k.at(*x)))).collect();
            Val::Con(*c, args.into())
        }
        Node::Tuple(xs) => Val::Tuple(xs.iter().map(|x| known_val(&k.at(*x))).collect()),
        // An array or a function has no form the type checker takes apart:
        // as it is.
        _ => known_val(k),
    }
}

/// Resolve solved metavariables at the head (no δ-unfolding).
pub fn force_meta(g: &Globals, v: Val) -> Val {
    match v {
        Val::Neutral(Head::Meta(m), sp) => match g.meta(m) {
            // A meta solved by another, solved in turn: the end of the chain,
            // remembered for `m` (a list literal's elements make a chain as
            // long as the list).
            Some(sol @ Val::Neutral(Head::Meta(_), _)) if sp.is_empty() => {
                let r = force_meta(g, sol);
                g.metas.borrow_mut()[m.0 as usize] = MetaEntry::Solved(r.clone());
                r
            }
            Some(sol) => {
                let mut r = sol;
                for e in sp.iter() {
                    r = elim(g, r, e.clone());
                }
                force_meta(g, r)
            }
            None => Val::Neutral(Head::Meta(m), sp),
        },
        Val::Known(k) => known_open(g, &k),
        v => v,
    }
}

/// Unfold one definition at the head, if allowed.
pub fn unfold(g: &Globals, v: &Val) -> Option<Val> {
    if let Val::Neutral(Head::Prim(p, args), sp) = v {
        // Evaluate a stuck primitive's arguments to weak-head form and retry it.
        let forced: Vec<Val> = args.iter().map(|a| force(g, a.clone())).collect();
        let mut r = prim_value(g, p, &forced)?;
        for e in sp.iter() {
            r = elim(g, r, e.clone());
        }
        return Some(r);
    }
    let Val::Neutral(Head::Def(d), sp) = v else { return None };
    let info = &g.defs[d.0 as usize];
    if info.body.is_none() {
        return builtin_value(g, info, sp);
    }
    let body = info.body.as_ref()?;
    if info.opaque || info.sealed {
        return None;
    }
    // Fuel bounds unfolding of functions, type functions too: one may
    // recurse without end until its termination check rejects it (#711). An
    // alias can't recurse, so unfolding it always ends and costs none:
    // running out of fuel must not stop `U8` from being `Nat`.
    if !info.alias {
        if g.fuel.get() == 0 {
            return None;
        }
        g.fuel.set(g.fuel.get() - 1);
    }
    match g.unfolds_left.get() {
        0 => return None,
        n => g.unfolds_left.set(n - 1),
    }
    let mut r = eval(g, &crate::core::Env::new(), body);
    for e in sp.iter() {
        r = elim(g, r, e.clone());
    }
    Some(r)
}

/// Is this the type of a type (or of a function returning one), as for a
/// type alias?
pub fn is_type_former(ty: &Tm) -> bool {
    let mut t = ty;
    while let Tm::Pi(_, _, _, _, b) = t {
        t = b;
    }
    matches!(t, Tm::Univ(_))
}

/// Pure builtins that types may need computed, on literal arguments: a
/// compile-time type such as `format_type (pieces (string.bytes s) 0 [])`
/// (§8.9).
fn builtin_value(g: &Globals, info: &DefInfo, sp: &[Elim]) -> Option<Val> {
    let q = format!("{}.{}", info.module, info.name);
    match (q.as_str(), sp) {
        ("std.string.bytes" | "std.utf8.encode", [Elim::App(a, _)]) => match force(g, a.clone()) {
            Val::Lit(Lit::Str(s)) => Some(Val::Lit(Lit::Bytes(Rc::from(s.as_bytes())))),
            _ => None,
        },
        _ => None,
    }
}

/// Is `v` the type `Nat`, or a refinement of it (`U8`, `Char`)? Aliases are
/// unfolded one at a time until `Nat` is met (#609): forcing would go past it
/// to `Int`.
pub fn is_nat(g: &Globals, v: &Val) -> bool {
    let Some(nat) = g.well_known.nat else { return false };
    let mut v = force_meta(g, v.clone());
    for _ in 0..64 {
        if let Val::Neutral(Head::Def(d), _) = &v {
            if *d == nat {
                return true;
            }
        }
        match unfold(g, &v) {
            Some(u) => v = force_meta(g, u),
            None => return false,
        }
    }
    false
}

/// The layout of an array of `v`, a type (#624): a fixed-width alias's or
/// `Bool`'s (`Ok(code)`, `checkers_rt::array::Layout`), a type variable at
/// level `Err(level)` (its layout is the variable's word at run time), or
/// one word per element (`Ok(0)`).
pub fn layout_of(g: &Globals, v: &Val) -> Result<u8, usize> {
    let mut v = force_meta(g, v.clone());
    for _ in 0..64 {
        if let Val::Neutral(Head::Def(d), _) = &v {
            if let Some((_, l)) = g.well_known.layouts.iter().find(|(a, _)| a == d) {
                return Ok(*l);
            }
        }
        match unfold(g, &v) {
            Some(u) => v = force_meta(g, u),
            None => break,
        }
    }
    match v {
        Val::TyCon(id, _) if Some(id) == g.well_known.bool_ty => Ok(checkers_rt::array::Layout::Bool as u8),
        Val::Neutral(Head::Var(x), sp) if sp.is_empty() => Err(x),
        _ => Ok(0),
    }
}

/// A type's descriptor (#170), as code builds it: what `checkers_rt::desc`
/// reads at run time.
#[derive(Clone, Debug)]
pub enum Desc {
    /// A type with its arguments' descriptors (none: a type without
    /// arguments, or one whose arguments aren't said).
    Known(u64, Vec<Desc>),
    /// The type variable at this level: its word at run time.
    Var(usize),
    /// A class's type kept in the dictionary at this level (#133).
    Dict(usize, ConId, usize),
    /// A type constructor variable at this level applied to arguments (M25).
    Apply(usize, Vec<Desc>),
    /// A value argument of a type, which its fields' types are computed
    /// from (`ByParam True`): the value, in the descriptor.
    Value(Val),
}

impl Desc {
    /// A type the descriptor doesn't name, laid out as `layout`.
    pub fn unknown(layout: u8) -> Desc {
        Desc::Known(checkers_rt::desc::tag(None, layout), Vec::new())
    }
}

/// The descriptor of `v`, a type (#170). Its layout is `layout_of`'s; a
/// type variable is its word at run time.
pub fn desc_of(g: &Globals, v: &Val) -> Desc {
    desc_at(g, v, 0)
}

fn desc_at(g: &Globals, v: &Val, depth: usize) -> Desc {
    let layout = match layout_of(g, v) {
        Ok(l) => l,
        Err(level) => return Desc::Var(level),
    };
    if depth > 32 {
        return Desc::unknown(layout);
    }
    match force(g, v.clone()) {
        Val::TyCon(id, args) => {
            let needed = value_params_needed(g, id);
            let ti = &g.tys[id.0 as usize];
            let args = args
                .iter()
                .enumerate()
                .map(|(k, a)| match ti.params.get(k) {
                    Some((_, t)) if is_type_former(t) => desc_at(g, a, depth + 1),
                    // A value parameter that a field's type is computed from.
                    _ if needed.contains(&k) => Desc::Value(a.clone()),
                    // Any other value parameter (`Vec a n`'s `n`) says
                    // nothing to show by.
                    _ => Desc::unknown(0),
                })
                .collect();
            Desc::Known(checkers_rt::desc::tag(Some(id.0), layout), args)
        }
        Val::TupleTy(ts) => {
            let parts = flat_parts(g, &ts, true);
            Desc::Known(checkers_rt::desc::tag(Some(checkers_rt::desc::TUPLE), 0), parts.iter().map(|t| desc_at(g, t, depth + 1)).collect())
        }
        Val::Neutral(Head::Var(x), sp) => match sp.as_slice() {
            [Elim::Field(c, i)] if g.is_dict_type_field(*c, *i) => Desc::Dict(x, *c, *i),
            sp if sp.iter().all(|e| matches!(e, Elim::App(..))) => Desc::Apply(
                x,
                sp.iter()
                    .map(|e| match e {
                        Elim::App(a, _) => desc_at(g, a, depth + 1),
                        _ => Desc::unknown(0),
                    })
                    .collect(),
            ),
            _ => Desc::unknown(layout),
        },
        // A type constructor written as a function (`\a -> Option a`, M25):
        // the type it applies to its argument, short of that argument.
        Val::Lam(_, _, _, c) => {
            const PROBE: usize = usize::MAX / 2;
            match force(g, apply_closure(g, &c, Val::var(PROBE))) {
                Val::TyCon(id, args) if matches!(args.last(), Some(Val::Neutral(Head::Var(PROBE), sp)) if sp.is_empty()) => {
                    match desc_at(g, &Val::TyCon(id, args[..args.len() - 1].into()), depth + 1) {
                        Desc::Known(tag, ds) => Desc::Known(tag, ds),
                        d => d,
                    }
                }
                _ => Desc::unknown(layout),
            }
        }
        _ => Desc::unknown(layout),
    }
}

/// The value parameters of type `id` that its fields' types are computed
/// from (#170), directly or through a type a field holds: their values go
/// in its descriptor.
pub fn value_params_needed(g: &Globals, id: TyId) -> std::collections::BTreeSet<usize> {
    if let Some(s) = g.value_params.borrow().get(&id) {
        return s.clone();
    }
    // Recursive types reach themselves: none, until worked out.
    g.value_params.borrow_mut().insert(id, Default::default());
    let mut out = std::collections::BTreeSet::new();
    let ti = &g.tys[id.0 as usize];
    let np = ti.params.len();
    let is_value = |l: usize| l < np && !is_type_former(&ti.params[l].1);
    for c in &ti.ctors {
        let ci = &g.cons[c.0 as usize];
        for k in 0..ci.fields.len() {
            if !g.is_runtime_field(*c, k) {
                continue;
            }
            let n = np + k;
            let env = (0..n).map(Val::var).collect::<crate::core::Env>();
            let v = force(g, eval(g, &env, &ci.fields[k].3));
            let mut levels = std::collections::BTreeSet::new();
            if fixed_type(&v) {
                value_args(g, &v, n, 0, &mut levels);
            } else {
                let mut free = std::collections::BTreeSet::new();
                free_vars(&quote(g, n, &v), 0, &mut free);
                levels.extend(free.into_iter().map(|i| n - 1 - i));
            }
            out.extend(levels.into_iter().filter(|l| is_value(*l)));
        }
    }
    g.value_params.borrow_mut().insert(id, out.clone());
    out
}

/// The levels (at `n`) that the value arguments in type `v` mention, at
/// the value parameters of the types it applies that their fields need.
fn value_args(g: &Globals, v: &Val, n: usize, depth: usize, out: &mut std::collections::BTreeSet<usize>) {
    if depth > 32 {
        return;
    }
    match force(g, v.clone()) {
        Val::TyCon(id, args) => {
            let needed = value_params_needed(g, id);
            let params = &g.tys[id.0 as usize].params;
            for (k, a) in args.iter().enumerate() {
                if params.get(k).is_some_and(|p| is_type_former(&p.1)) {
                    value_args(g, a, n, depth + 1, out);
                } else if needed.contains(&k) {
                    let mut free = std::collections::BTreeSet::new();
                    free_vars(&quote(g, n, a), 0, &mut free);
                    out.extend(free.into_iter().map(|i| n - 1 - i));
                }
            }
        }
        Val::TupleTy(ts) => ts.iter().for_each(|t| value_args(g, t, n, depth + 1, out)),
        _ => {}
    }
}

/// Whether a type (forced) is a type former applied, not computed from
/// values: a type, a tuple or function type, or a type variable (applied).
fn fixed_type(v: &Val) -> bool {
    match v {
        Val::Neutral(Head::Var(_), sp) => sp.iter().all(|e| matches!(e, Elim::App(..))) || matches!(sp.as_slice(), [Elim::Field(..)]),
        Val::Neutral(..) => false,
        _ => true,
    }
}

/// Whether a descriptor holds a value (`Desc::Value`).
fn has_value(d: &Desc) -> bool {
    match d {
        Desc::Value(_) => true,
        Desc::Known(_, xs) | Desc::Apply(_, xs) => xs.iter().any(has_value),
        _ => false,
    }
}

/// How a constructor's field has its type (#170).
pub enum FieldType {
    /// From its type's parameters alone: a descriptor template says it.
    Fixed,
    /// Computed when the value is shown, from earlier fields (`v~(if
    /// is_text then String else Int)`) or from value parameters of its
    /// type (`ByParam b`), which its descriptor holds: this type, in the
    /// context of the parameters and earlier fields.
    FromFields(Tm),
    /// Computed from a field that isn't kept when the program runs (this
    /// level: the type's parameters, then the fields).
    NotKept(usize),
}

/// How field `k` of constructor `c` has its type.
pub fn field_type(g: &Globals, c: ConId, k: usize) -> FieldType {
    let ci = &g.cons[c.0 as usize];
    let np = g.arity_ty(ci.ty);
    let n = np + k;
    let env = (0..n).map(Val::var).collect::<crate::core::Env>();
    let v = force(g, eval(g, &env, &ci.fields[k].3));
    let t = quote(g, n, &v);
    if fixed_type(&v) {
        // A type holding a value its own fields need (`ByParam b`), from
        // this type's: computed when shown, as the value is known then.
        return if has_value(&desc_of(g, &v)) { FieldType::FromFields(t) } else { FieldType::Fixed };
    }
    let mut free = std::collections::BTreeSet::new();
    free_vars(&t, 0, &mut free);
    for i in free {
        let level = n - 1 - i;
        if level >= np && !g.is_runtime_field(c, level - np) {
            return FieldType::NotKept(level);
        }
    }
    FieldType::FromFields(t)
}

/// The literal the type checker's evaluation reaches from `v`, unfolding
/// the definitions it may (not a sealed function's body, §6) within
/// `DEFAULT_FUEL` steps of its own: the quick way to a value known at
/// compile time (§8.9; `Elab::known_value` runs the rest). `None` if it
/// reaches no literal.
pub fn known_lit(g: &Globals, v: Val) -> Option<Lit> {
    let saved = g.fuel.replace(DEFAULT_FUEL);
    let r = force(g, v);
    g.fuel.set(saved);
    match r {
        Val::Lit(l) => Some(l),
        _ => None,
    }
}

/// The value of constant `d` (a `let`) if it is known at compile time:
/// `Globals::known`, which code generation then uses.
pub fn known_const(g: &Globals, d: DefId) -> Option<Tm> {
    g.known.borrow().get(&d).cloned()
}

/// Weak-head normal form: resolve metas and unfold definitions at the
/// head. A closed call that takes `KEEP_STEPS` unfoldings or more is
/// kept across builds (§8.9, `known_cache::force_kept`).
pub fn force(g: &Globals, v: Val) -> Val {
    let v = force_meta(g, v);
    if matches!(v, Val::Neutral(Head::Def(_), _)) && g.keeping.get() {
        return crate::known_cache::force_kept(g, v);
    }
    unfold_all(g, v)
}

/// `force` of `v`, whose metas at the head are resolved: computed here,
/// not kept.
#[inline]
pub fn unfold_all(g: &Globals, mut v: Val) -> Val {
    while let Some(u) = unfold(g, &v) {
        v = force_meta(g, u);
    }
    v
}

/// A class's type at a known instance (#133), as the instance gives it:
/// `Seq.Elem (Array U8)` is `U8`, the alias kept, so its refinement is known
/// (#190). `None` if `v` isn't one, or its dictionary isn't known.
pub fn class_type_at(g: &Globals, v: &Val) -> Option<Val> {
    let is_class_type = |v: &Val| matches!(v, Val::Neutral(Head::Def(d), sp) if g.assoc_def(*d).is_some_and(|(_, _, n)| sp.len() == n + 1));
    let mut v = force_meta(g, v.clone());
    if !is_class_type(&v) {
        return None;
    }
    // Unfold the class's type, then its dictionary, until the field is read.
    for _ in 0..32 {
        let reading = is_class_type(&v) || matches!(&v, Val::Neutral(Head::Def(_), sp) if sp.iter().any(|e| matches!(e, Elim::Field(..))));
        if !reading {
            // Stuck on a dictionary that is a variable: not known.
            let stuck = matches!(&v, Val::Neutral(_, sp) if sp.iter().any(|e| matches!(e, Elim::Field(..))));
            return (!stuck).then_some(v);
        }
        v = force_meta(g, unfold(g, &v)?);
    }
    None
}

/// A neutral value with one more eliminator: the spine is copied only if
/// another value shares it, so applying a neutral to n arguments one at a
/// time copies none of them.
fn with_elim(h: Head, mut sp: Rc<Vec<Elim>>, e: Elim) -> Val {
    Rc::make_mut(&mut sp).push(e);
    Val::Neutral(h, sp)
}

pub fn elim(g: &Globals, v: Val, e: Elim) -> Val {
    match e {
        Elim::App(a, i) => app(g, v, a, i),
        Elim::Proj(i, rest) => proj(g, v, i, rest),
        Elim::Field(c, i) => field(g, v, c, i),
        Elim::Case(c, env) => case(g, v, c, env),
    }
}

pub fn app(g: &Globals, f: Val, a: Val, i: Icit) -> Val {
    match force_meta(g, f) {
        Val::Lam(_, _, _, c) => apply_closure(g, &c, a),
        Val::Neutral(h, sp) => with_elim(h, sp, Elim::App(a, i)),
        _ => Val::Error,
    }
}

/// The value to attach a stuck eliminator to: the original if it is neutral.
fn stuck_base(g: &Globals, orig: Val, forced: Val) -> Val {
    match force_meta(g, orig) {
        v @ Val::Neutral(..) => v,
        _ => forced,
    }
}

/// A tuple's components, flattened: a last component that is itself a tuple
/// (of two or more) is its components (#673). `ty`: of a tuple type.
pub fn flat_parts(g: &Globals, vs: &[Val], ty: bool) -> Vec<Val> {
    flat_parts_by(vs, |v| match (ty, force(g, v.clone())) {
        (true, Val::TupleTy(ws)) | (false, Val::Tuple(ws)) => Some(ws),
        _ => None,
    })
}

/// `flat_parts`, with `parts` saying which last component is a tuple, and
/// its components.
pub fn flat_parts_by(vs: &[Val], parts: impl Fn(&Val) -> Option<Rc<[Val]>>) -> Vec<Val> {
    let mut vs = vs.to_vec();
    while vs.len() >= 2 {
        match parts(&vs[vs.len() - 1]) {
            Some(ws) if ws.len() >= 2 => {
                vs.pop();
                vs.extend(ws.iter().cloned());
            }
            _ => break,
        }
    }
    vs
}

/// Two flattened tuples' (or tuple types') components, paired: of
/// different lengths, the shorter's last component is the rest of the
/// longer, `(a, t)` and `(A, B, C)` giving `a`, `A` and `t`, `(B, C)`.
/// `None` if no pairing makes them alike: the shorter has fewer than two.
pub fn pair_parts(x: Vec<Val>, y: Vec<Val>, ty: bool) -> Option<(Vec<Val>, Vec<Val>)> {
    if x.len() == y.len() {
        return Some((x, y));
    }
    let (short, long, flip) = if x.len() < y.len() { (x, y, false) } else { (y, x, true) };
    if short.len() < 2 {
        return None;
    }
    let k = short.len() - 1;
    let rest = if ty { Val::TupleTy(long[k..].into()) } else { Val::Tuple(long[k..].into()) };
    let mut long2 = long[..k].to_vec();
    long2.push(rest);
    Some(if flip { (long2, short) } else { (short, long2) })
}

// A projection or a field read doesn't unfold what it reads: a call's
// result stays a call until something needs its value (`force`, which
// unfolds the head and reads the field then). Reading a field of
// `wrap (build 4000 [])` must not run `build` while checking. A field that
// holds a type is read at once: it is a type checking needs (a class's type
// from its instance's dictionary, `Seq.Elem String` is `Char`).

fn proj(g: &Globals, v: Val, i: usize, rest: bool) -> Val {
    match force_meta(g, v) {
        Val::Tuple(vs) => {
            let vs = flat_parts(g, &vs, false);
            match vs.len() {
                n if rest && n > i + 1 => Val::Tuple(vs[i..].into()),
                _ => vs.get(i).cloned().unwrap_or(Val::Error),
            }
        }
        Val::Neutral(h, sp) => with_elim(h, sp, Elim::Proj(i, rest)),
        _ => Val::Error,
    }
}

fn field(g: &Globals, v: Val, c: ConId, i: usize) -> Val {
    match force_meta(g, v) {
        // A string literal's bytes (#170).
        Val::Lit(Lit::Str(s)) if Some(g.cons[c.0 as usize].ty) == g.well_known.string => Val::Lit(Lit::Bytes(Rc::from(s.as_bytes()))),
        Val::Con(_, args) => {
            let np = g.arity_ty(g.cons[c.0 as usize].ty);
            args.get(np + i).cloned().unwrap_or(Val::Error)
        }
        v @ Val::Neutral(..) if g.is_type_field(c, i) => match force(g, v.clone()) {
            f @ (Val::Con(..) | Val::Lit(_)) => field(g, f, c, i),
            f @ Val::Neutral(..) => match stuck_base(g, v, f) {
                Val::Neutral(h, sp) => with_elim(h, sp, Elim::Field(c, i)),
                _ => Val::Error,
            },
            _ => Val::Error,
        },
        Val::Neutral(h, sp) => with_elim(h, sp, Elim::Field(c, i)),
        _ => Val::Error,
    }
}

fn case(g: &Globals, v: Val, c: Rc<CaseTm>, env: Env) -> Val {
    match force(g, v.clone()) {
        Val::Con(id, args) => {
            for (cid, n, body) in &c.branches {
                if *cid == id {
                    let fields = &args[args.len() - n..];
                    let mut e = env.clone();
                    e.extend(fields.iter().cloned());
                    return eval(g, &e, body);
                }
            }
            match &c.default {
                Some(d) => eval(g, &env, d),
                None => Val::Error,
            }
        }
        Val::Lit(l) => {
            for (lit, body) in &c.lits {
                if *lit == l {
                    return eval(g, &env, body);
                }
            }
            // A string literal matched as `String b`: its bytes (#170).
            if let Lit::Str(s) = &l {
                if let Some((_, n, body)) = c.branches.iter().find(|(cid, _, _)| Some(g.cons[cid.0 as usize].ty) == g.well_known.string) {
                    let mut e = env.clone();
                    e.extend(std::iter::repeat_n(Val::Lit(Lit::Bytes(Rc::from(s.as_bytes()))), *n));
                    return eval(g, &e, body);
                }
            }
            match &c.default {
                Some(d) => eval(g, &env, d),
                None => Val::Error,
            }
        }
        f @ Val::Neutral(..) => match stuck_base(g, v, f) {
            Val::Neutral(h, sp) => with_elim(h, sp, Elim::Case(c, env)),
            _ => Val::Error,
        },
        _ => Val::Error,
    }
}

fn num(v: &Val) -> Option<i128> {
    match v {
        Val::Lit(Lit::Num(n)) => Some(*n),
        _ => None,
    }
}

/// Structural equality of closed values; None if it can't be decided yet.
fn val_eq(g: &Globals, a: &Val, b: &Val) -> Option<bool> {
    if let (Val::Known(x), Val::Known(y)) = (a, b) {
        return Some(x.same(y));
    }
    match (force(g, a.clone()), force(g, b.clone())) {
        (Val::Lit(x), Val::Lit(y)) => Some(x == y),
        (Val::Con(c1, a1), Val::Con(c2, a2)) => {
            if c1 != c2 {
                return Some(false);
            }
            let np = g.arity_ty(g.cons[c1.0 as usize].ty);
            for (x, y) in a1[np..].iter().zip(&a2[np..]) {
                match val_eq(g, x, y) {
                    Some(true) => {}
                    other => return other,
                }
            }
            Some(true)
        }
        (Val::Tuple(x), Val::Tuple(y)) => {
            let (x, y) = (flat_parts(g, &x, false), flat_parts(g, &y, false));
            if x.len() != y.len() {
                return None;
            }
            for (a, b) in x.iter().zip(&y) {
                match val_eq(g, a, b) {
                    Some(true) => {}
                    other => return other,
                }
            }
            Some(true)
        }
        _ => None,
    }
}

/// Apply a primitive. Like a definition, it does not unfold its arguments:
/// if they are not already values it stays stuck, and `unfold` evaluates
/// it further only when conversion checking needs to.
fn prim(g: &Globals, p: &Prim, orig: Vec<Val>) -> Val {
    let args: Vec<Val> = orig.into_iter().map(|a| force_meta(g, a)).collect();
    match prim_value(g, p, &args) {
        Some(v) => v,
        None => Val::Neutral(Head::Prim(p.clone(), args.into()), Rc::new(Vec::new())),
    }
}

/// An integer value's literal as a `BigInt`: arithmetic's slow path, when
/// an operand is `Big` or the `i128` result would overflow.
fn big(v: &Val) -> Option<BigInt> {
    match v {
        Val::Lit(l) => l.as_int(),
        _ => None,
    }
}

fn prim_value(g: &Globals, p: &Prim, args: &[Val]) -> Option<Val> {
    let n2 = || Some((num(&args[0])?, num(&args[1])?));
    let b2 = || Some((big(&args[0])?, big(&args[1])?));
    let lit = |n: BigInt| Val::Lit(Lit::int(n));
    // `i128` arithmetic, or `BigInt` arithmetic where that overflows.
    let arith = |fast: fn(i128, i128) -> Option<i128>, slow: fn(BigInt, BigInt) -> Option<BigInt>| match n2() {
        Some((a, b)) => match fast(a, b) {
            Some(n) => Some(Val::Lit(Lit::Num(n))),
            None => slow(a.into(), b.into()).map(lit),
        },
        None => b2().and_then(|(a, b)| slow(a, b)).map(lit),
    };
    let order = || match n2() {
        Some((a, b)) => Some(a.cmp(&b)),
        None => b2().map(|(a, b)| a.cmp(&b)),
    };
    let cmp = |f: fn(std::cmp::Ordering) -> bool| order().map(|o| g.bool_val(f(o)));
    let r = match p {
        Prim::Add => arith(|a, b| a.checked_add(b), |a, b| Some(a + b)),
        // `Sub` carries its operand type: on `Nat`, `a - b` with `a < b` has no value (stuck).
        Prim::Sub => {
            let on_nat = args.get(2).is_some_and(|t| is_nat(g, t));
            match order() {
                Some(std::cmp::Ordering::Less) if on_nat => None,
                _ => arith(|a, b| a.checked_sub(b), |a, b| Some(a - b)),
            }
        }
        Prim::Mul => arith(|a, b| a.checked_mul(b), |a, b| Some(a * b)),
        Prim::Div => arith(|a, b| a.checked_div_euclid(b), |a, b| (!b.is_zero()).then(|| a.div_euclid(&b))),
        Prim::Rem => arith(|a, b| a.checked_rem_euclid(b), |a, b| (!b.is_zero()).then(|| a.rem_euclid(&b))),
        Prim::Neg => match num(&args[0]) {
            Some(a) => Some(a.checked_neg().map_or_else(|| lit(-BigInt::from(a)), |n| Val::Lit(Lit::Num(n)))),
            None => big(&args[0]).map(|a| lit(-a)),
        },
        Prim::Lt => cmp(|o| o.is_lt()),
        Prim::Le => cmp(|o| o.is_le()),
        Prim::Gt => cmp(|o| o.is_gt()),
        Prim::Ge => cmp(|o| o.is_ge()),
        Prim::Eq => val_eq(g, &args[0], &args[1]).map(|b| g.bool_val(b)),
        Prim::Ne => val_eq(g, &args[0], &args[1]).map(|b| g.bool_val(!b)),
        Prim::Concat => match (&args[0], &args[1]) {
            (Val::Lit(Lit::Str(a)), Val::Lit(Lit::Str(b))) => Some(Val::Lit(Lit::Str(Rc::from(format!("{a}{b}"))))),
            (Val::Lit(Lit::Bytes(a)), Val::Lit(Lit::Bytes(b))) => {
                Some(Val::Lit(Lit::Bytes(a.iter().chain(b.iter()).copied().collect())))
            }
            _ => None,
        },
        Prim::Len => match &args[0] {
            Val::Lit(Lit::Bytes(b)) => Some(Val::Lit(Lit::Num(b.len() as i128))),
            Val::Lit(Lit::Str(s)) => Some(Val::Lit(Lit::Num(s.len() as i128))),
            _ => None,
        },
        Prim::Index => match (&args[0], num(&args[1])) {
            (Val::Lit(Lit::Bytes(b)), Some(i)) if i >= 0 && (i as usize) < b.len() => {
                Some(Val::Lit(Lit::Num(b[i as usize] as i128)))
            }
            _ => None,
        },
        Prim::Par => Some(args[0].clone()),
        _ => None,
    };
    r
}

// ── quoting ──────────────────────────────────────────────────────────────────

pub fn quote(g: &Globals, l: usize, v: &Val) -> Tm {
    if let Val::Known(k) = v {
        return Tm::Known(k.clone());
    }
    match force_meta(g, v.clone()) {
        Val::Neutral(h, sp) => {
            let mut t = match h {
                Head::Var(x) => Tm::Var(l - x - 1),
                Head::Meta(m) => Tm::Meta(m),
                Head::Def(d) => Tm::Def(d),
                Head::Prim(p, args) => Tm::PrimApp(p, args.iter().map(|a| quote(g, l, a)).collect()),
            };
            for e in sp.iter() {
                t = match e {
                    Elim::App(a, i) => Tm::App(Rc::new(t), Rc::new(quote(g, l, a)), *i, Mult::Many),
                    Elim::Proj(i, r) => Tm::Proj(Rc::new(t), *i, *r),
                    Elim::Field(c, i) => Tm::Field(Rc::new(t), *c, *i),
                    Elim::Case(c, env) => Tm::Case(Rc::new(t), quote_case(g, l, c, env)),
                };
            }
            t
        }
        Val::Lam(x, m, i, c) => Tm::Lam(x, m, i, Rc::new(quote(g, l + 1, &apply_closure(g, &c, Val::var(l))))),
        Val::Pi(x, m, i, a, c) => Tm::Pi(
            x,
            m,
            i,
            Rc::new(quote(g, l, &a)),
            Rc::new(quote(g, l + 1, &apply_closure(g, &c, Val::var(l)))),
        ),
        Val::Univ(u) => Tm::Univ(u),
        Val::TyCon(t, args) => Tm::TyConApp(t, args.iter().map(|a| quote(g, l, a)).collect()),
        Val::Con(c, args) => Tm::ConApp(c, args.iter().map(|a| quote(g, l, a)).collect()),
        Val::Lit(x) => Tm::Lit(x),
        Val::TupleTy(vs) => Tm::TupleTy(vs.iter().map(|a| quote(g, l, a)).collect()),
        Val::Tuple(vs) => Tm::Tuple(vs.iter().map(|a| quote(g, l, a)).collect()),
        Val::Known(k) => Tm::Known(k),
        Val::Error => Tm::Error,
    }
}

fn quote_case(g: &Globals, l: usize, c: &Rc<CaseTm>, env: &Env) -> Rc<CaseTm> {
    let qb = |n: usize, body: &Tm| {
        let mut e = env.clone();
        for k in 0..n {
            e.push(Val::var(l + k));
        }
        quote(g, l + n, &eval(g, &e, body))
    };
    Rc::new(CaseTm {
        branches: c.branches.iter().map(|(cid, n, b)| (*cid, *n, qb(*n, b))).collect(),
        lits: c.lits.iter().map(|(lit, b)| (lit.clone(), qb(0, b))).collect(),
        default: c.default.as_ref().map(|b| qb(0, b)),
    })
}

// ── unification ──────────────────────────────────────────────────────────────

/// Why unification failed, where a message can say more than "mismatch".
#[derive(Debug, Clone, Copy)]
pub enum UnifyError {
    Mismatch,
    /// `?f x` against a type that isn't a type constructor applied to a
    /// type (`Int`), #627.
    NotApplied(MetaId),
}

/// What an unknown stands for (#627): the implicit parameter `name` of
/// `owner`, a meta applied to `spine` locals first.
#[derive(Debug, Clone)]
pub struct MetaOrigin {
    pub name: Name,
    pub owner: Option<Name>,
    pub spine: usize,
    /// Its parameter is a type (`a~Type`) or a type constructor (arity > 0).
    pub is_type: bool,
    pub arity: usize,
}

struct PartialRenaming {
    dom: usize,
    cod: usize,
    ren: HashMap<usize, usize>,
}

fn invert(g: &Globals, gamma: usize, sp: &[Elim]) -> Result<(PartialRenaming, Vec<Icit>), UnifyError> {
    let mut ren = HashMap::new();
    let mut icits = Vec::new();
    // A variable given twice (`?m x x`, a lambda's result type applied to a
    // variable already in its context) can't be told apart in the
    // solution: it is left out of the renaming, so a solution that doesn't
    // mention it (`Int`) is found and one that does fails as out of scope.
    let mut twice = std::collections::HashSet::new();
    for (dom, e) in sp.iter().enumerate() {
        match e {
            Elim::App(a, i) => match force(g, a.clone()) {
                Val::Neutral(Head::Var(x), s) if s.is_empty() => {
                    if ren.insert(x, dom).is_some() {
                        twice.insert(x);
                    }
                    icits.push(*i);
                }
                _ => return Err(UnifyError::Mismatch),
            },
            _ => return Err(UnifyError::Mismatch),
        }
    }
    for x in twice {
        ren.remove(&x);
    }
    Ok((PartialRenaming { dom: sp.len(), cod: gamma, ren }, icits))
}

fn lift(p: &PartialRenaming) -> PartialRenaming {
    let mut ren = p.ren.clone();
    ren.insert(p.cod, p.dom);
    PartialRenaming { dom: p.dom + 1, cod: p.cod + 1, ren }
}

fn rename(g: &Globals, m: MetaId, p: &PartialRenaming, v: &Val) -> Result<Tm, UnifyError> {
    let go_sp = |t: Tm, sp: &Rc<Vec<Elim>>| -> Result<Tm, UnifyError> {
        let mut t = t;
        for e in sp.iter() {
            t = match e {
                Elim::App(a, i) => Tm::App(Rc::new(t), Rc::new(rename(g, m, p, a)?), *i, Mult::Many),
                Elim::Proj(i, r) => Tm::Proj(Rc::new(t), *i, *r),
                Elim::Field(c, i) => Tm::Field(Rc::new(t), *c, *i),
                Elim::Case(c, env) => Tm::Case(Rc::new(t), rename_case(g, m, p, c, env)?),
            };
        }
        Ok(t)
    };
    // Closed: as it is.
    if let Val::Known(k) = v {
        return Ok(Tm::Known(k.clone()));
    }
    match force_meta(g, v.clone()) {
        Val::Neutral(Head::Meta(m2), sp) => {
            if m2 == m {
                return Err(UnifyError::Mismatch); // occurs check
            }
            match prune(g, m2, &sp, p) {
                Some(m3) => go_sp(Tm::Meta(m3.0), &Rc::new(m3.1)),
                None => go_sp(Tm::Meta(m2), &sp),
            }
        }
        Val::Neutral(Head::Var(x), sp) => match p.ren.get(&x) {
            Some(x2) => go_sp(Tm::Var(p.dom - x2 - 1), &sp),
            None => Err(UnifyError::Mismatch), // scope error
        },
        Val::Neutral(Head::Def(d), sp) => go_sp(Tm::Def(d), &sp),
        Val::Neutral(Head::Prim(pr, args), sp) => {
            let args = args.iter().map(|a| rename(g, m, p, a)).collect::<Result<Vec<_>, _>>()?;
            go_sp(Tm::PrimApp(pr, args), &sp)
        }
        Val::Lam(x, mu, i, c) => Ok(Tm::Lam(
            x,
            mu,
            i,
            Rc::new(rename(g, m, &lift(p), &apply_closure(g, &c, Val::var(p.cod)))?),
        )),
        Val::Pi(x, mu, i, a, c) => Ok(Tm::Pi(
            x,
            mu,
            i,
            Rc::new(rename(g, m, p, &a)?),
            Rc::new(rename(g, m, &lift(p), &apply_closure(g, &c, Val::var(p.cod)))?),
        )),
        Val::Univ(u) => Ok(Tm::Univ(u)),
        Val::TyCon(t, args) => {
            Ok(Tm::TyConApp(t, args.iter().map(|a| rename(g, m, p, a)).collect::<Result<_, _>>()?))
        }
        Val::Con(c, args) => Ok(Tm::ConApp(c, args.iter().map(|a| rename(g, m, p, a)).collect::<Result<_, _>>()?)),
        Val::Lit(l) => Ok(Tm::Lit(l)),
        Val::TupleTy(vs) => Ok(Tm::TupleTy(vs.iter().map(|a| rename(g, m, p, a)).collect::<Result<_, _>>()?)),
        Val::Tuple(vs) => Ok(Tm::Tuple(vs.iter().map(|a| rename(g, m, p, a)).collect::<Result<_, _>>()?)),
        Val::Known(k) => Ok(Tm::Known(k)),
        Val::Error => Ok(Tm::Error),
    }
}

/// Pruning: `?m2 x y`, where `y` is out of the solution's scope, can only
/// not depend on `y`. So `?m2 := λx y. ?m3 x`, and the solution mentions
/// `?m3 x` (an unknown made inside a `match` arm, in a type the `match`
/// has outside it). `None` when every argument is in scope, or one isn't a
/// variable (then nothing is pruned).
fn prune(g: &Globals, m2: MetaId, sp: &[Elim], p: &PartialRenaming) -> Option<(MetaId, Vec<Elim>)> {
    let mut keep = Vec::new();
    for e in sp {
        match e {
            Elim::App(a, i) => match force(g, a.clone()) {
                Val::Neutral(Head::Var(x), s) if s.is_empty() => keep.push((p.ren.contains_key(&x), *i, a.clone())),
                _ => return None,
            },
            _ => return None,
        }
    }
    if keep.iter().all(|k| k.0) {
        return None;
    }
    let m3 = g.fresh_meta();
    let origin = g.meta_origins.borrow().get(&m2).cloned();
    if let Some(o) = origin {
        let spine = keep.iter().filter(|k| k.0).count();
        g.meta_origins.borrow_mut().insert(m3, MetaOrigin { spine, ..o });
    }
    let n = keep.len();
    let mut t = Tm::Meta(m3);
    for (k, (kept, i, _)) in keep.iter().enumerate() {
        if *kept {
            t = Tm::App(Rc::new(t), Rc::new(Tm::Var(n - 1 - k)), *i, Mult::Many);
        }
    }
    for (k, (_, i, _)) in keep.iter().enumerate().rev() {
        t = Tm::Lam(Rc::from(format!("x{k}")), Mult::Many, *i, Rc::new(t));
    }
    let sol = eval(g, &crate::core::Env::new(), &t);
    g.metas.borrow_mut()[m2.0 as usize] = MetaEntry::Solved(sol);
    Some((m3, keep.into_iter().filter(|k| k.0).map(|k| Elim::App(k.2, k.1)).collect()))
}

/// An unknown whose spine mentions variables at or above `outer` (a
/// lambda's parameters, for its inferred result type) solved by one that
/// doesn't, when the spine is all variables: the result type then can't
/// depend on the parameters, so the lambda can be applied to anything,
/// not only to distinct variables.
pub fn strengthen(g: &Globals, v: &Val, outer: usize) -> Val {
    let v = force_meta(g, v.clone());
    if let Val::Neutral(Head::Meta(m), sp) = &v {
        let ren: HashMap<usize, usize> = (0..outer).map(|x| (x, x)).collect();
        let p = PartialRenaming { dom: outer, cod: outer, ren };
        if prune(g, *m, sp, &p).is_some() {
            return force_meta(g, v.clone());
        }
    }
    v
}

/// Each unsolved unknown in `t` (a term over `l` variables) applied to the
/// variable at level `x` solved by one that isn't, when its spine is all
/// variables: what `t` says can then no longer depend on `x` through an
/// unknown that nothing determined (an implicit argument a function type's
/// predicate left open must not make it look like a postcondition, #576).
pub fn forget_var(g: &Globals, l: usize, t: &Tm, x: usize) {
    if let Tm::Meta(m) = t.head() {
        if g.meta(*m).is_none() {
            let env = (0..l).map(Val::var).collect::<crate::core::Env>();
            if let Val::Neutral(Head::Meta(m), sp) = force_meta(g, eval(g, &env, t)) {
                let ren: HashMap<usize, usize> = (0..l).filter(|y| *y != x).map(|y| (y, y)).collect();
                prune(g, m, &sp, &PartialRenaming { dom: l, cod: l, ren });
            }
        }
    }
    t.each_sub(|s, n| forget_var(g, l + n, s, x));
}

fn rename_case(g: &Globals, m: MetaId, p: &PartialRenaming, c: &Rc<CaseTm>, env: &Env) -> Result<Rc<CaseTm>, UnifyError> {
    let rb = |n: usize, body: &Tm| -> Result<Tm, UnifyError> {
        let mut e = env.clone();
        let mut pr = PartialRenaming { dom: p.dom, cod: p.cod, ren: p.ren.clone() };
        for _ in 0..n {
            e.push(Val::var(pr.cod));
            pr = lift(&pr);
        }
        rename(g, m, &pr, &eval(g, &e, body))
    };
    Ok(Rc::new(CaseTm {
        branches: c.branches.iter().map(|(cid, n, b)| Ok((*cid, *n, rb(*n, b)?))).collect::<Result<_, _>>()?,
        lits: c.lits.iter().map(|(lit, b)| Ok((lit.clone(), rb(0, b)?))).collect::<Result<_, _>>()?,
        default: c.default.as_ref().map(|b| rb(0, b)).transpose()?,
    }))
}

fn solve(g: &Globals, gamma: usize, m: MetaId, sp: &[Elim], rhs: &Val) -> Result<(), UnifyError> {
    let (pren, icits) = invert(g, gamma, sp)?;
    let body = rename(g, m, &pren, rhs)?;
    let mut t = body;
    for (k, i) in icits.iter().enumerate().rev() {
        t = Tm::Lam(Rc::from(format!("x{k}")), Mult::Many, *i, Rc::new(t));
    }
    let sol = eval(g, &crate::core::Env::new(), &t);
    g.metas.borrow_mut()[m.0 as usize] = MetaEntry::Solved(sol);
    Ok(())
}

fn unify_sp(g: &Globals, l: usize, a: &[Elim], b: &[Elim]) -> Result<(), UnifyError> {
    if a.len() != b.len() {
        return Err(UnifyError::Mismatch);
    }
    for (x, y) in a.iter().zip(b) {
        match (x, y) {
            (Elim::App(u, _), Elim::App(v, _)) => unify(g, l, u, v)?,
            (Elim::Proj(i, a), Elim::Proj(j, b)) if i == j && a == b => {}
            (Elim::Field(c1, i), Elim::Field(c2, j)) if c1 == c2 && i == j => {}
            (Elim::Case(c1, e1), Elim::Case(c2, e2)) => {
                let q1 = quote_case(g, l, c1, e1);
                let q2 = quote_case(g, l, c2, e2);
                if !tm_eq(&Tm::Case(Rc::new(Tm::Error), q1), &Tm::Case(Rc::new(Tm::Error), q2)) {
                    return Err(UnifyError::Mismatch);
                }
            }
            _ => return Err(UnifyError::Mismatch),
        }
    }
    Ok(())
}

/// Syntactic equality of quoted terms (used for stuck case trees).
pub fn tm_eq(a: &Tm, b: &Tm) -> bool {
    format!("{a:?}") == format!("{b:?}")
}

fn unify_many(g: &Globals, l: usize, a: &[Val], b: &[Val]) -> Result<(), UnifyError> {
    if a.len() != b.len() {
        return Err(UnifyError::Mismatch);
    }
    for (x, y) in a.iter().zip(b) {
        unify(g, l, x, y)?;
    }
    Ok(())
}

/// Two tuples (or tuple types), flattened (#673). Of different lengths, the
/// shorter's last component is the rest of the longer: `(a, t)` and
/// `(A, B, C)` give `a = A`, `t = (B, C)`.
fn unify_tuple(g: &Globals, l: usize, x: &[Val], y: &[Val], ty: bool) -> Result<(), UnifyError> {
    let (x, y) = pair_parts(flat_parts(g, x, ty), flat_parts(g, y, ty), ty).ok_or(UnifyError::Mismatch)?;
    unify_many(g, l, &x, &y)
}

pub fn unify(g: &Globals, l: usize, a: &Val, b: &Val) -> Result<(), UnifyError> {
    // Two known values: equal or not, compared without recursion.
    if let (Val::Known(x), Val::Known(y)) = (a, b) {
        return if x.same(y) { Ok(()) } else { Err(UnifyError::Mismatch) };
    }
    let a = force_meta(g, a.clone());
    let b = force_meta(g, b.clone());
    let r = unify_whnf(g, l, &a, &b);
    if r.is_ok() {
        return r;
    }
    // A class's type with a base type, at a dictionary that is a variable
    // (#360), is a subtype of its base: compared as it, here, up to
    // refinement; which way a value may go is the refinements' check. Its
    // base is found before it is unfolded (`Encoding.Unit s` names `s`).
    let (abase, bbase) = (class_type_base(g, &a), class_type_base(g, &b));
    // Retry after unfolding a definition at either head.
    if let Some(a2) = unfold(g, &a) {
        let r2 = unify(g, l, &a2, &b);
        return match (r2, abase) {
            (Err(_), Some(base)) => unify(g, l, &base, &b),
            (r2, _) => r2,
        };
    }
    if let Some(b2) = unfold(g, &b) {
        let r2 = unify(g, l, &a, &b2);
        return match (r2, bbase) {
            (Err(_), Some(base)) => unify(g, l, &a, &base),
            (r2, _) => r2,
        };
    }
    if let Some(a2) = abase {
        return unify(g, l, &a2, &b);
    }
    if let Some(b2) = bbase {
        return unify(g, l, &a, &b2);
    }
    r
}

/// The base type of a class's type read from a dictionary that is a
/// variable (`Encoding.Unit s` in generic code, #360), if it has one: its
/// first base type, at the class's arguments and the dictionary. Read
/// from the dictionary alone (`$d.$Unit`), only a base type that doesn't
/// name the class's parameters is known.
pub fn class_type_base(g: &Globals, v: &Val) -> Option<Val> {
    if g.type_bases.is_empty() {
        return None;
    }
    let v = force_meta(g, v.clone());
    // `C.Name a {d}`.
    if let Val::Neutral(Head::Def(d), sp) = &v {
        let (c, i, n) = g.assoc_def(*d)?;
        if sp.len() != n + 1 {
            return None;
        }
        let args: Vec<Val> = sp.iter().map(|e| if let Elim::App(a, _) = e { Some(a.clone()) } else { None }).collect::<Option<_>>()?;
        if !matches!(force(g, args[n].clone()), Val::Neutral(Head::Var(_), _)) {
            return None;
        }
        let b = g.type_bases.get(&(c, i))?.first()?;
        return Some(eval(g, &crate::core::Env::from(args), b));
    }
    let Val::Neutral(Head::Var(h), sp) = force(g, v) else { return None };
    let Some(Elim::Field(c, i)) = sp.last() else { return None };
    let b = g.type_bases.get(&(*c, *i))?.first()?;
    let mut fv = std::collections::BTreeSet::new();
    free_vars(b, 0, &mut fv);
    // Over the parameters, then the dictionary (index 0).
    if fv.iter().any(|&x| x > 0) {
        return None;
    }
    let n = g.arity_ty(g.cons[c.0 as usize].ty);
    let mut env: Vec<Val> = vec![Val::Error; n];
    env.push(Val::Neutral(Head::Var(h), Rc::new(sp[..sp.len() - 1].to_vec())));
    Some(eval(g, &crate::core::Env::from(env), b))
}

/// The unknowns in a term.
fn metas_in(t: &Tm, out: &mut std::collections::HashSet<MetaId>) {
    if let Tm::Meta(m) = t {
        out.insert(*m);
    }
    t.any_sub(|s, _| {
        metas_in(s, out);
        false
    });
}

fn unify_whnf(g: &Globals, l: usize, a: &Val, b: &Val) -> Result<(), UnifyError> {
    match (a, b) {
        (Val::Error, Val::Error) => Ok(()),
        // An error is any type: the unknowns it is compared with stay
        // unknown, because of it.
        (Val::Error, other) | (other, Val::Error) => {
            let mut out = g.errored.borrow_mut();
            metas_in(&zonk_metas(g, l, &quote(g, l, other)), &mut out);
            Ok(())
        }
        (Val::Lam(_, _, _, c1), Val::Lam(_, _, _, c2)) => {
            unify(g, l + 1, &apply_closure(g, c1, Val::var(l)), &apply_closure(g, c2, Val::var(l)))
        }
        (Val::Lam(_, _, i, c), other) | (other, Val::Lam(_, _, i, c)) => {
            let x = Val::var(l);
            let lhs = apply_closure(g, c, x.clone());
            let rhs = app(g, other.clone(), x, *i);
            unify(g, l + 1, &lhs, &rhs)
        }
        (Val::Pi(_, m1, i1, a1, c1), Val::Pi(_, m2, i2, a2, c2)) => {
            if i1 != i2 || m1 != m2 {
                return Err(UnifyError::Mismatch);
            }
            unify(g, l, a1, a2)?;
            unify(g, l + 1, &apply_closure(g, c1, Val::var(l)), &apply_closure(g, c2, Val::var(l)))
        }
        (Val::Univ(x), Val::Univ(y)) if x == y => Ok(()),
        (Val::TyCon(t1, a1), Val::TyCon(t2, a2)) if t1 == t2 => {
            // A type's header's dictionaries (#385) are fixed by its other
            // arguments: one instance per class and types (coherence). Two
            // found differently (a clause's, an instance's) are the same
            // dictionary, so they are compared only to learn an unknown.
            let ti = &g.tys[t1.0 as usize];
            let n = ti.params.len() - ti.dicts;
            if ti.dicts == 0 || a1.len() != a2.len() || a1.len() <= n {
                return unify_many(g, l, a1, a2);
            }
            unify_many(g, l, &a1[..n], &a2[..n])?;
            for (x, y) in a1[n..].iter().zip(&a2[n..]) {
                let _ = unify(g, l, x, y);
            }
            Ok(())
        }
        (Val::Con(c1, a1), Val::Con(c2, a2)) if c1 == c2 => unify_many(g, l, a1, a2),
        (Val::Lit(x), Val::Lit(y)) if x == y => Ok(()),
        (Val::TupleTy(x), Val::TupleTy(y)) => unify_tuple(g, l, x, y, true),
        (Val::Tuple(x), Val::Tuple(y)) => unify_tuple(g, l, x, y, false),
        (Val::Neutral(Head::Meta(m1), s1), Val::Neutral(Head::Meta(m2), s2)) if m1 == m2 => unify_sp(g, l, s1, s2),
        (Val::Neutral(Head::Meta(m1), s1), Val::Neutral(Head::Meta(m2), s2)) => {
            // Solve the meta with the larger scope first; fall back to the other.
            if s1.len() >= s2.len() {
                solve(g, l, *m1, s1, b).or_else(|_| solve(g, l, *m2, s2, a))
            } else {
                solve(g, l, *m2, s2, a).or_else(|_| solve(g, l, *m1, s1, b))
            }
        }
        // A class's type at a dictionary not found yet (#133): it doesn't
        // tell which, so the comparison waits until it is found.
        (Val::Neutral(Head::Meta(_), sp), _) | (_, Val::Neutral(Head::Meta(_), sp))
            if sp.iter().any(|e| matches!(e, Elim::Field(c, i) if g.is_type_field(*c, *i))) =>
        {
            g.postponed.borrow_mut().push((l, a.clone(), b.clone()));
            Ok(())
        }
        (Val::Neutral(Head::Meta(m), sp), other) | (other, Val::Neutral(Head::Meta(m), sp)) => {
            solve(g, l, *m, sp, other)
                .or_else(|e| first_order(g, l, *m, sp, other).unwrap_or(Err(e)))
                .or_else(|e| invert_case(g, l, *m, sp, other).unwrap_or(Err(e)))
        }
        (Val::Neutral(Head::Var(x), s1), Val::Neutral(Head::Var(y), s2)) if x == y => unify_sp(g, l, s1, s2),
        (Val::Neutral(Head::Def(x), s1), Val::Neutral(Head::Def(y), s2)) if x == y => unify_sp(g, l, s1, s2),
        (Val::Neutral(Head::Prim(p1, a1), s1), Val::Neutral(Head::Prim(p2, a2), s2)) if p1 == p2 => {
            unify_many(g, l, a1, a2)?;
            unify_sp(g, l, s1, s2)
        }
        _ => Err(UnifyError::Mismatch),
    }
}

// ── printing ─────────────────────────────────────────────────────────────────

/// The names of a context's locals, outermost first, as a persistent list:
/// keeping them for a later message, as each deferred constraint does,
/// takes no copy however many locals are in scope.
#[derive(Clone, Default)]
pub struct Names(Option<Rc<NamesCell>>);

struct NamesCell {
    name: Name,
    len: usize,
    outer: Names,
}

impl Names {
    pub fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |c| c.len)
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }
    pub fn push(&mut self, name: Name) {
        let outer = std::mem::take(self);
        *self = Names(Some(Rc::new(NamesCell { name, len: outer.len() + 1, outer })));
    }
    pub fn pop(&mut self) {
        if let Some(c) = &self.0 {
            *self = c.outer.clone();
        }
    }
    pub fn truncate(&mut self, n: usize) {
        while self.len() > n {
            self.pop();
        }
    }
    /// Innermost first.
    pub fn iter(&self) -> impl Iterator<Item = &Name> {
        std::iter::successors(self.0.as_deref(), |c| c.outer.0.as_deref()).map(|c| &c.name)
    }
    /// The name at `level`.
    pub fn get(&self, level: usize) -> Option<&Name> {
        self.iter().nth(self.len().checked_sub(1 + level)?)
    }
    /// The level of the innermost local named `x`.
    pub fn level_of(&self, x: &str) -> Option<usize> {
        self.iter().position(|n| n.as_ref() == x).map(|k| self.len() - 1 - k)
    }
    /// Outermost first, as levels count.
    pub fn to_vec(&self) -> Vec<Name> {
        let mut v: Vec<Name> = self.iter().cloned().collect();
        v.reverse();
        v
    }
}

/// Outermost first.
impl FromIterator<Name> for Names {
    fn from_iter<I: IntoIterator<Item = Name>>(it: I) -> Names {
        let mut names = Names::default();
        for n in it {
            names.push(n);
        }
        names
    }
}

impl Drop for Names {
    /// One cell at a time: dropping a long list recursively would use stack
    /// in proportion to it.
    fn drop(&mut self) {
        let mut cur = self.0.take();
        while let Some(c) = cur {
            match Rc::try_unwrap(c) {
                Ok(mut cell) => cur = cell.outer.0.take(),
                Err(_) => break,
            }
        }
    }
}

impl std::fmt::Debug for Names {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.to_vec()).finish()
    }
}

/// The names of the locals a shown term may mention, outermost first: read
/// where they are, so that showing a term doesn't copy its whole context.
pub trait Scope {
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// The name of the local at `level`, below `len`.
    fn name(&self, level: usize) -> &Name;
    /// Where the local at `level` is bound, if known.
    fn at(&self, _level: usize) -> Option<u32> {
        None
    }
    /// How many locals are named `x`.
    fn count(&self, x: &str) -> usize {
        (0..self.len()).filter(|l| &**self.name(*l) == x).count()
    }
}

impl Scope for [Name] {
    fn len(&self) -> usize {
        <[Name]>::len(self)
    }
    fn name(&self, level: usize) -> &Name {
        &self[level]
    }
}

impl Scope for Vec<Name> {
    fn len(&self) -> usize {
        Vec::len(self)
    }
    fn name(&self, level: usize) -> &Name {
        &self[level]
    }
}

impl<const N: usize> Scope for [Name; N] {
    fn len(&self) -> usize {
        N
    }
    fn name(&self, level: usize) -> &Name {
        &self[level]
    }
}

/// A scope with more names inside it.
pub struct Under<'a, S: Scope + ?Sized>(pub &'a S, pub &'a [Name]);

impl<S: Scope + ?Sized> Scope for Under<'_, S> {
    fn len(&self) -> usize {
        self.0.len() + self.1.len()
    }
    fn name(&self, level: usize) -> &Name {
        match level.checked_sub(self.0.len()) {
            Some(k) => &self.1[k],
            None => self.0.name(level),
        }
    }
    fn at(&self, level: usize) -> Option<u32> {
        if level < self.0.len() { self.0.at(level) } else { None }
    }
    fn count(&self, x: &str) -> usize {
        self.0.count(x) + self.1.iter().filter(|n| &***n == x).count()
    }
}

/// The names `show_prec` sees: the context's, then the binders it is under.
struct Ns<'a, S: Scope + ?Sized> {
    outer: &'a S,
    inner: Vec<Name>,
    /// Mark the context's locals whose names another has (`show_marked`).
    mark_locals: bool,
}

impl<S: Scope + ?Sized> Ns<'_, S> {
    fn len(&self) -> usize {
        self.outer.len() + self.inner.len()
    }
    /// The name of de Bruijn index `i`.
    fn get(&self, i: usize) -> Option<&Name> {
        match self.inner.len().checked_sub(1 + i) {
            Some(k) => Some(&self.inner[k]),
            None => self.outer.len().checked_sub(1 + i - self.inner.len()).map(|l| self.outer.name(l)),
        }
    }
    fn contains(&self, x: &Name) -> bool {
        self.inner.contains(x) || self.outer.count(x) > 0
    }
    fn push(&mut self, x: Name) {
        self.inner.push(x);
    }
    fn pop(&mut self) {
        self.inner.pop();
    }
}

/// Render a core term for error messages. `names` are the local variable
/// names, innermost last.
pub fn show<S: Scope + ?Sized>(g: &Globals, names: &S, t: &Tm) -> String {
    let mut ns = Ns { outer: names, inner: Vec::new(), mark_locals: false };
    show_prec(g, &mut ns, t, 0)
}

thread_local! {
    /// Whether `show_prec` marks the globals it names (`show_marked`).
    static MARKING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Starts a global's mark: `MARK kind id MARK_NAME name MARK_END`, where
/// `kind` is `d` (a definition), `t` (a type) or `c` (a constructor); or
/// a local's, `MARK v level.at.hidden MARK_NAME name MARK_END`.
const MARK: char = '\u{1}';
const MARK_NAME: char = '\u{2}';
const MARK_END: char = '\u{3}';

/// A global as named in a message: by `show_marked`, marked with which
/// declaration it is, so a diagnostic can tell apart two of the same name
/// (`unmark`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Marked {
    Def(DefId),
    Ty(TyId),
    Con(ConId),
    /// A local of the context, one of several of its name there: its
    /// level, where it is bound, and, if a later local of its name hides
    /// it, where that one is bound.
    /// `avoid` has bit `k - 1` set when a local of the context is named
    /// this name followed by `k` (`a1`): a number to show it by isn't one.
    Var { level: u32, at: Option<u32>, hidden_by: Option<Option<u32>>, avoid: u64 },
}

fn global(m: Marked, name: &str) -> String {
    if !MARKING.with(|c| c.get()) {
        return name.to_string();
    }
    let id = match m {
        Marked::Def(d) => format!("d{}", d.0),
        Marked::Ty(t) => format!("t{}", t.0),
        Marked::Con(c) => format!("c{}", c.0),
        Marked::Var { level, at, hidden_by, avoid } => {
            let pos = |a: Option<u32>| a.map_or("-".to_string(), |a| a.to_string());
            match hidden_by {
                Some(by) => format!("v{level}.{}.h{}.{avoid}", pos(at), pos(by)),
                None => format!("v{level}.{}.s.{avoid}", pos(at)),
            }
        }
    };
    format!("{MARK}{id}{MARK_NAME}{name}{MARK_END}")
}

/// The local at `level` of the context, named `name`, as a message names
/// it: marked when another local of the context has its name.
fn local<S: Scope + ?Sized>(ls: &S, level: usize, name: &Name) -> String {
    if !MARKING.with(|c| c.get()) {
        return name.to_string();
    }
    let same = |l: &usize| ls.name(*l) == name;
    if level >= ls.len() || ls.count(name) < 2 {
        return name.to_string();
    }
    let hidden_by = (level + 1..ls.len()).rev().find(same).map(|l| ls.at(l));
    let mut avoid = 0u64;
    for l in 0..ls.len() {
        if let Some(k) = ls.name(l).strip_prefix(&**name).and_then(|k| k.parse::<u32>().ok()).filter(|k| (1..=64).contains(k)) {
            avoid |= 1 << (k - 1);
        }
    }
    global(Marked::Var { level: level as u32, at: ls.at(level), hidden_by, avoid }, name)
}

/// `show`, with each global it names marked with its declaration: text for
/// a diagnostic, which `unmark` turns into names. A local of the context
/// whose name another has is marked too, with where each is bound, as far
/// as `names` knows (`Scope::at`).
pub fn show_marked<S: Scope + ?Sized>(g: &Globals, names: &S, t: &Tm) -> String {
    let was = MARKING.with(|c| c.replace(true));
    let mut ns = Ns { outer: names, inner: Vec::new(), mark_locals: true };
    let s = show_prec(g, &mut ns, t, 0);
    MARKING.with(|c| c.set(was));
    s
}

/// The globals marked in `s`, with their names, in order.
pub fn marks(s: &str) -> Vec<(Marked, String)> {
    let mut out = Vec::new();
    unmark(s, &mut |m, n| {
        out.push((m, n.to_string()));
        n.to_string()
    });
    out
}

/// `s` with its marks dropped: each global by its name as declared.
pub fn plain(s: &str) -> String {
    unmark(s, &mut |_, n| n.to_string())
}

/// `s` with each marked global replaced by `name(global, its name)`.
pub fn unmark(s: &str, name: &mut dyn FnMut(Marked, &str) -> String) -> String {
    if !s.contains(MARK) {
        return s.to_string();
    }
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    while let Some(i) = rest.find(MARK) {
        out.push_str(&rest[..i]);
        let after = &rest[i + MARK.len_utf8()..];
        let parsed = after.find(MARK_NAME).and_then(|j| {
            let k = after[j..].find(MARK_END)? + j;
            let (kind, id) = after[..j].split_at(after[..j].char_indices().nth(1).map_or(j, |x| x.0));
            let m = match kind {
                "d" => Marked::Def(DefId(id.parse().ok()?)),
                "t" => Marked::Ty(TyId(id.parse().ok()?)),
                "c" => Marked::Con(ConId(id.parse().ok()?)),
                "v" => {
                    let mut p = id.split('.');
                    let pos = |a: &str| if a == "-" { Some(None) } else { a.parse().ok().map(Some) };
                    let level = p.next()?.parse().ok()?;
                    let at = pos(p.next()?)?;
                    let hidden_by = match p.next()? {
                        "s" => None,
                        h => Some(pos(h.strip_prefix('h')?)?),
                    };
                    let avoid = p.next()?.parse().ok()?;
                    Marked::Var { level, at, hidden_by, avoid }
                }
                _ => return None,
            };
            Some((m, &after[j + MARK_NAME.len_utf8()..k], &after[k + MARK_END.len_utf8()..]))
        });
        match parsed {
            Some((m, n, next)) => {
                out.push_str(&name(m, n));
                rest = next;
            }
            None => {
                rest = after;
            }
        }
    }
    out.push_str(rest);
    out
}

fn fresh<S: Scope + ?Sized>(ns: &Ns<S>, x: &Name) -> Name {
    if x.as_ref() == "_" {
        return x.clone();
    }
    let mut cand = x.clone();
    let mut k = 1;
    while ns.contains(&cand) {
        cand = Rc::from(format!("{x}{k}"));
        k += 1;
    }
    cand
}

/// A match on `Bool` as the operator it shows: its precedence (`and` 3,
/// `or` 2, `implies` 1, `if` 0) and its operands (for `if`, the condition
/// and the `then` branch; for `or`, the `else` branch is the second).
fn bool_op<'a>(g: &Globals, t: &'a Tm) -> Option<(u8, &'a Tm, &'a Tm)> {
    let Tm::Case(s, c) = t else { return None };
    let wk = &g.well_known;
    let arm = |con: Option<ConId>| c.branches.iter().find(|b| Some(b.0) == con).map(|b| &b.2);
    let (Some(tb), Some(fb), 2) = (arm(wk.true_con), arm(wk.false_con), c.branches.len()) else { return None };
    let lit = |x: &Tm, v: Option<ConId>| matches!(x, Tm::Con(k) if Some(*k) == v) || matches!(x, Tm::ConApp(k, xs) if Some(*k) == v && xs.is_empty());
    Some(if lit(fb, wk.false_con) {
        (3, s, tb)
    } else if lit(tb, wk.true_con) {
        (2, s, fb)
    } else if lit(fb, wk.true_con) {
        (1, s, tb)
    } else {
        (0, s, tb)
    })
}

fn paren(b: bool, s: String) -> String {
    if b {
        format!("({s})")
    } else {
        s
    }
}

fn show_prec<S: Scope + ?Sized>(g: &Globals, ns: &mut Ns<S>, t: &Tm, p: u8) -> String {
    match t {
        Tm::Var(i) => {
            let level = ns.len().wrapping_sub(1 + i);
            match ns.get(*i) {
                // A local of the context (not one bound inside `t`).
                Some(n) if ns.mark_locals && level < ns.outer.len() => local(ns.outer, level, n),
                Some(n) => n.to_string(),
                None => format!("#{i}"),
            }
        }
        Tm::Def(d) if is_anon_alias(g, *d) => g.defs[d.0 as usize].name.to_string(),
        Tm::Def(d) => global(Marked::Def(*d), &g.defs[d.0 as usize].name),
        Tm::TyCon(t) => global(Marked::Ty(*t), &g.tys[t.0 as usize].name),
        Tm::Con(c) => global(Marked::Con(*c), &g.cons[c.0 as usize].name),
        Tm::Meta(m) => match g.meta(*m) {
            Some(v) => show_prec(g, ns, &quote(g, ns.len(), &v), p),
            // An unknown the checker has not worked out yet: by the
            // parameter it stands for (#627), else `_`.
            None => match g.meta_origins.borrow().get(m) {
                Some(o) => format!("?{}", o.name),
                None => "_".into(),
            },
        },
        Tm::Univ(0) => "Type".into(),
        Tm::Univ(u) => format!("Type {u}"),
        Tm::Pi(x, m, i, a, b) => {
            let dom = show_prec(g, ns, a, 1);
            let x2 = fresh(ns, x);
            ns.push(x2.clone());
            let cod = show_prec(g, ns, b, 0);
            ns.pop();
            let mul = match m {
                Mult::Zero => "ghost ",
                Mult::One => "own ",
                Mult::Many => "",
            };
            let anon_dom = matches!(head_def(a), Some(d) if is_anon_alias(g, d));
            let s = match i {
                Icit::Expl if anon_dom && *m != Mult::Zero => format!("{mul}{dom} -> {cod}"),
                // A dictionary (`$d0`, #615): its class clause alone.
                Icit::Impl if x.starts_with("$d") => format!("{{{dom}}} -> {cod}"),
                Icit::Impl => format!("{{{x2}~{mul}{dom}}} -> {cod}"),
                Icit::Expl if x.as_ref() == "_" && *m == Mult::Many => format!("{dom} -> {cod}"),
                Icit::Expl => format!("({x2}~{mul}{dom}) -> {cod}"),
            };
            paren(p > 0, s)
        }
        Tm::Lam(x, _, _, b) => {
            let x2 = fresh(ns, x);
            ns.push(x2.clone());
            let s = format!("\\{x2} -> {}", show_prec(g, ns, b, 0));
            ns.pop();
            paren(p > 0, s)
        }
        Tm::App(..) => {
            let mut args = Vec::new();
            let mut h = t;
            while let Tm::App(f, a, i, _) = h {
                if *i == Icit::Expl {
                    args.push(a.clone());
                }
                h = f;
            }
            args.reverse();
            // An inline refinement (#576) prints as written.
            if let Tm::Def(d) = h {
                if is_anon_alias(g, *d) {
                    return g.defs[d.0 as usize].name.to_string();
                }
            }
            if let Tm::Meta(m) = h {
                if g.meta(*m).is_none() {
                    // Applied to the locals in scope where it was made, then
                    // to its own arguments (`?f Int`).
                    let Some(o) = g.meta_origins.borrow().get(m).cloned() else { return "_".into() };
                    let own: Vec<_> = args.iter().skip(o.spine).collect();
                    if own.is_empty() {
                        return format!("?{}", o.name);
                    }
                    let mut s = format!("?{}", o.name);
                    for a in own {
                        s += " ";
                        s += &show_prec(g, ns, a, 2);
                    }
                    return paren(p > 1, s);
                }
            }
            if args.is_empty() {
                return show_prec(g, ns, h, p);
            }
            let mut s = show_prec(g, ns, h, 2);
            for a in args {
                s += " ";
                s += &show_prec(g, ns, &a, 2);
            }
            paren(p > 1, s)
        }
        Tm::Let(x, _, _, v, b) => {
            let vs = show_prec(g, ns, v, 0);
            ns.push(x.clone());
            let s = format!("let {x} = {vs}; {}", show_prec(g, ns, b, 0));
            ns.pop();
            paren(p > 0, s)
        }
        Tm::Known(k) => k.show(g, p),
        Tm::Lit(Lit::Num(n)) => n.to_string(),
        Tm::Lit(Lit::Big(n)) => n.to_string(),
        Tm::Lit(Lit::Str(s)) => format!("{s:?}"),
        Tm::Lit(Lit::Bytes(b)) => format!("b{:?}", String::from_utf8_lossy(b)),
        Tm::TupleTy(ts) if ts.is_empty() => "Unit".into(),
        Tm::TupleTy(ts) | Tm::Tuple(ts) => {
            format!("({})", ts.iter().map(|x| show_prec(g, ns, x, 0)).collect::<Vec<_>>().join(", "))
        }
        Tm::Proj(x, i, _) => format!("{}.{i}", show_prec(g, ns, x, 2)),
        Tm::Field(x, c, i) => {
            let f = &g.cons[c.0 as usize].fields[*i].0;
            format!("{}.{f}", show_prec(g, ns, x, 2))
        }
        Tm::TyConApp(ty, args) => {
            let ti = &g.tys[ty.0 as usize];
            // Its header's dictionaries are never shown (#385).
            let args = &args[..args.len().min(ti.params.len() - ti.dicts)];
            if args.is_empty() {
                return global(Marked::Ty(*ty), &ti.name);
            }
            let s = format!(
                "{} {}",
                global(Marked::Ty(*ty), &ti.name),
                args.iter().map(|a| show_prec(g, ns, a, 2)).collect::<Vec<_>>().join(" ")
            );
            paren(p > 1, s)
        }
        Tm::ConApp(c, args) => {
            let ci = &g.cons[c.0 as usize];
            let np = g.arity_ty(ci.ty);
            if c.0 as usize == g.well_known.cons.map(|c| c.0 as usize).unwrap_or(usize::MAX) && args.len() == np + 2 {
                let s = format!("{} :: {}", show_prec(g, ns, &args[np], 3), show_prec(g, ns, &args[np + 1], 1));
                return paren(p > 0, s);
            }
            let explicit: Vec<&Tm> = args[np..]
                .iter()
                .zip(&ci.fields)
                .filter(|(_, f)| f.2 == Icit::Expl)
                .map(|(a, _)| a)
                .collect();
            if explicit.is_empty() {
                if Some(*c) == g.well_known.nil {
                    return "[]".into();
                }
                return global(Marked::Con(*c), &ci.name);
            }
            let s = format!(
                "{} {}",
                global(Marked::Con(*c), &ci.name),
                explicit.iter().map(|a| show_prec(g, ns, a, 2)).collect::<Vec<_>>().join(" ")
            );
            paren(p > 1, s)
        }
        Tm::PrimApp(pr, args) => {
            let op = match pr {
                Prim::Add => Some("+"),
                Prim::Sub => Some("-"),
                Prim::Mul => Some("*"),
                Prim::Div => Some("/"),
                Prim::Rem => Some("%"),
                Prim::Eq => Some("=="),
                Prim::Ne => Some("!="),
                Prim::Lt => Some("<"),
                Prim::Le => Some("<="),
                Prim::Gt => Some(">"),
                Prim::Ge => Some(">="),
                Prim::Concat => Some("++"),
                _ => None,
            };
            match (op, args.as_slice()) {
                (Some(o), [a, b]) | (Some(o), [a, b, _]) => {
                    paren(p > 0, format!("{} {o} {}", show_prec(g, ns, a, 2), show_prec(g, ns, b, 2)))
                }
                _ => {
                    if let (Prim::Effect(_), [a]) = (pr, args.as_slice()) {
                        return show_prec(g, ns, a, p);
                    }
                    if let (Prim::Neg, [a]) = (pr, args.as_slice()) {
                        return format!("-{}", show_prec(g, ns, a, 2));
                    }
                    if let (Prim::Index, [a, i, ..]) = (pr, args.as_slice()) {
                        return format!("{}[{}]", show_prec(g, ns, a, 3), show_prec(g, ns, i, 0));
                    }
                    let name = match pr {
                        Prim::Builtin(n) => n.to_string(),
                        Prim::Len => "len".into(),
                        Prim::Index => "index".into(),
                        Prim::Neg => "negate".into(),
                        other => format!("{other:?}").to_lowercase(),
                    };
                    let s = format!(
                        "{name} {}",
                        args.iter().map(|a| show_prec(g, ns, a, 2)).collect::<Vec<_>>().join(" ")
                    );
                    paren(p > 1, s)
                }
            }
        }
        Tm::Case(s, _) => {
            // `if`, `and`, `or` and `implies` are matches on `Bool`.
            if let Some((op, a, b)) = bool_op(g, t) {
                // An operand binding less tightly than the operator is put
                // in parentheses: `and` over `or` over `implies`, which
                // groups to the right.
                let level = |x: &Tm| bool_op(g, x).map_or(4, |o| o.0);
                let side = |ns: &mut Ns<S>, x: &Tm, min: u8| paren(level(x) < min, show_prec(g, ns, x, 0));
                let text = match op {
                    3 => format!("{} and {}", side(ns, a, 3), side(ns, b, 3)),
                    2 => format!("{} or {}", side(ns, a, 2), side(ns, b, 2)),
                    1 => format!("{} implies {}", side(ns, a, 2), side(ns, b, 1)),
                    _ => {
                        let Tm::Case(_, c) = t else { unreachable!() };
                        let f = c.branches.iter().find(|x| Some(x.0) == g.well_known.false_con).map(|x| &x.2);
                        let fs = f.map(|f| show_prec(g, ns, f, 0)).unwrap_or_default();
                        format!("if {} then {} else {fs}", show_prec(g, ns, a, 0), show_prec(g, ns, b, 0))
                    }
                };
                return paren(p > 0, text);
            }
            paren(p > 0, format!("match {} …", show_prec(g, ns, s, 0)))
        }
        Tm::Error => "_".into(),
    }
}

/// The free variables of `t` under `depth` binders, as indices from outside
/// those binders.
pub fn free_vars(t: &Tm, depth: usize, out: &mut std::collections::BTreeSet<usize>) {
    match t {
        Tm::Var(i) if *i >= depth => {
            out.insert(i - depth);
        }
        _ => t.each_sub(|x, n| free_vars(x, depth + n, out)),
    }
}

/// The largest free variable of `t`, if it has one: an environment of one
/// more variable than that is enough to evaluate `t`.
pub fn max_var(t: &Tm) -> Option<usize> {
    let mut vars = std::collections::BTreeSet::new();
    free_vars(t, 0, &mut vars);
    vars.last().copied()
}

/// `t` with each free variable `i` (an index from outside `depth` binders)
/// replaced by `f(i)`.
pub fn rename_free(t: &Tm, depth: usize, f: &dyn Fn(usize) -> usize) -> Tm {
    match t {
        Tm::Var(i) if *i >= depth => Tm::Var(f(i - depth) + depth),
        _ => t.map_sub(|x, n| rename_free(x, depth + n, f)),
    }
}

/// The definitions a term mentions.
pub fn defs_in(t: &Tm, out: &mut Vec<DefId>) {
    match t {
        Tm::Def(d) => out.push(*d),
        _ => t.each_sub(|x, _| defs_in(x, out)),
    }
}

/// An inline refinement `(n~Int, n >= 5)` (#576): an alias with no name of
/// its own, named by its text.
pub fn is_anon_alias(g: &Globals, d: DefId) -> bool {
    g.defs[d.0 as usize].name.starts_with('(')
}

/// The definition at the head of an application, if any.
pub fn head_def(t: &Tm) -> Option<DefId> {
    match t {
        Tm::Def(d) => Some(*d),
        Tm::App(f, ..) => head_def(f),
        _ => None,
    }
}

/// Replace each solved meta in `t` (a term over `l` variables), with its
/// arguments, by its solution, leaving the rest of `t` as it is.
pub fn zonk_metas(g: &Globals, l: usize, t: &Tm) -> Tm {
    // One pass: `None` when nothing under a node changes, so unchanged
    // subterms are shared, not copied (this was quadratic: a walk to find a
    // solved meta at every node).
    fn go(g: &Globals, l: usize, t: &Tm) -> Option<Tm> {
        let h = t.head();
        if let Tm::Meta(m) = h {
            if g.meta(*m).is_some() {
                return Some(fix_mults(g, &quote(g, l, &eval(g, &g.id_env(l), t))));
            }
        }
        let rc = |x: &Rc<Tm>, k: usize| go(g, l + k, x).map(Rc::new);
        let keep = |new: Option<Rc<Tm>>, old: &Rc<Tm>| new.unwrap_or_else(|| old.clone());
        let many = |v: &[Tm]| -> Option<Vec<Tm>> {
            let new: Vec<Option<Tm>> = v.iter().map(|x| go(g, l, x)).collect();
            if new.iter().all(|x| x.is_none()) {
                return None;
            }
            Some(new.into_iter().zip(v).map(|(n, o)| n.unwrap_or_else(|| o.clone())).collect())
        };
        match t {
            Tm::App(f, a, i, m) => {
                let (nf, na) = (rc(f, 0), rc(a, 0));
                (nf.is_some() || na.is_some()).then(|| Tm::App(keep(nf, f), keep(na, a), *i, *m))
            }
            Tm::Pi(x, m, i, a, b) => {
                let (na, nb) = (rc(a, 0), rc(b, 1));
                (na.is_some() || nb.is_some()).then(|| Tm::Pi(x.clone(), *m, *i, keep(na, a), keep(nb, b)))
            }
            Tm::Lam(x, m, i, b) => rc(b, 1).map(|nb| Tm::Lam(x.clone(), *m, *i, nb)),
            Tm::Let(x, m, a, b, c) => {
                let (na, nb, nc) = (rc(a, 0), rc(b, 0), rc(c, 1));
                (na.is_some() || nb.is_some() || nc.is_some()).then(|| Tm::Let(x.clone(), *m, keep(na, a), keep(nb, b), keep(nc, c)))
            }
            Tm::TyConApp(c, v) => many(v).map(|v| Tm::TyConApp(*c, v)),
            Tm::ConApp(c, v) => many(v).map(|v| Tm::ConApp(*c, v)),
            Tm::TupleTy(v) => many(v).map(Tm::TupleTy),
            Tm::Tuple(v) => many(v).map(Tm::Tuple),
            Tm::PrimApp(p, v) => many(v).map(|v| Tm::PrimApp(p.clone(), v)),
            Tm::Proj(x, i, r) => rc(x, 0).map(|nx| Tm::Proj(nx, *i, *r)),
            Tm::Field(x, c, i) => rc(x, 0).map(|nx| Tm::Field(nx, *c, *i)),
            Tm::Case(sc, c) => {
                let ns = rc(sc, 0);
                let nb: Vec<Option<Tm>> = c.branches.iter().map(|(_, n, b)| go(g, l + n, b)).collect();
                let nl: Vec<Option<Tm>> = c.lits.iter().map(|(_, b)| go(g, l, b)).collect();
                let nd = c.default.as_ref().map(|b| go(g, l, b));
                let changed = ns.is_some() || nb.iter().any(|x| x.is_some()) || nl.iter().any(|x| x.is_some()) || matches!(nd, Some(Some(_)));
                changed.then(|| {
                    Tm::Case(
                        keep(ns, sc),
                        Rc::new(CaseTm {
                            branches: c.branches.iter().zip(nb).map(|((k, n, b), x)| (*k, *n, x.unwrap_or_else(|| b.clone()))).collect(),
                            lits: c.lits.iter().zip(nl).map(|((v, b), x)| (v.clone(), x.unwrap_or_else(|| b.clone()))).collect(),
                            default: c.default.as_ref().zip(nd).map(|(b, x)| x.unwrap_or_else(|| b.clone())),
                        }),
                    )
                })
            }
            _ => None,
        }
    }
    go(g, l, t).unwrap_or_else(|| t.clone())
}

/// A quoted application of a definition, with each argument's multiplicity
/// taken from the definition's type again (quoting doesn't keep them).
fn fix_mults(g: &Globals, t: &Tm) -> Tm {
    let mut args = Vec::new();
    let mut h = t;
    while let Tm::App(f, a, i, _) = h {
        args.push((fix_mults(g, a), *i));
        h = f;
    }
    args.reverse();
    let Tm::Def(d) = h else { return t.clone() };
    let mut ty = g.defs[d.0 as usize].ty.clone();
    let mut out = h.clone();
    for (a, i) in args {
        let m = match &ty {
            Tm::Pi(_, m, _, _, b) => {
                let m = *m;
                ty = (**b).clone();
                m
            }
            _ => Mult::Many,
        };
        out = Tm::App(Rc::new(out), Rc::new(a), i, m);
    }
    out
}

/// `?f x =?= t a` where pattern unification fails (`?f` applied to a type
/// that isn't a bound variable, M25): solve the heads and the arguments
/// apart, as Haskell does for type constructors. `t a` is a variable or a
/// type constructor applied to arguments.
/// The head of a value, for inverting a function by it (#659).
#[derive(PartialEq)]
enum RigidHead {
    TyCon(TyId),
    Con(ConId),
    Tuple,
    Pi,
    Univ(u32),
}

fn rigid_head(v: &Val) -> Option<RigidHead> {
    Some(match v {
        Val::TyCon(t, _) => RigidHead::TyCon(*t),
        Val::Con(c, _) => RigidHead::Con(*c),
        Val::TupleTy(ts) | Val::Tuple(ts) if ts.len() >= 2 => RigidHead::Tuple,
        Val::Pi(..) => RigidHead::Pi,
        Val::Univ(u) => RigidHead::Univ(*u),
        _ => return None,
    })
}

/// #659: a `match` stuck on an unknown (`futures ?ts`, unfolded) must equal a
/// value with a rigid head (`(Future Nat, Future String)`). If every arm of
/// the `match` gives a different rigid head ("constructor-headed", as in
/// Agda), the arm with the value's head is the only one that can: the
/// unknown is that arm's constructor, its fields fresh unknowns.
fn invert_case(g: &Globals, l: usize, m: MetaId, sp: &[Elim], other: &Val) -> Option<Result<(), UnifyError>> {
    let (Elim::Case(c, env), args) = sp.split_last()? else { return None };
    if !args.iter().all(|e| matches!(e, Elim::App(..))) || !c.lits.is_empty() || c.default.is_some() {
        return None;
    }
    let want = rigid_head(&force(g, other.clone()))?;
    let mut heads = Vec::new();
    let mut found = None;
    for (con, n, body) in &c.branches {
        let mut e = env.clone();
        // The fields, unknown: far above any context.
        e.extend((0..*n).map(|k| Val::var(usize::MAX / 2 + k)));
        let h = rigid_head(&force(g, eval(g, &e, body)))?;
        if heads.contains(&h) {
            return None;
        }
        if h == want {
            found = Some(*con);
        }
        heads.push(h);
    }
    let con = found?;
    let info = &g.cons[con.0 as usize];
    let n = g.tys[info.ty.0 as usize].params.len() + info.fields.len();
    // Fresh unknowns in the same context as `m`: applied to the same arguments.
    let fresh: Rc<[Val]> = (0..n).map(|_| Val::Neutral(Head::Meta(g.fresh_meta()), Rc::new(args.to_vec()))).collect();
    if solve(g, l, m, args, &Val::Con(con, fresh)).is_err() {
        return None;
    }
    Some(unify(g, l, &Val::Neutral(Head::Meta(m), Rc::new(sp.to_vec())), other))
}

fn first_order(g: &Globals, l: usize, m: MetaId, sp: &[Elim], other: &Val) -> Option<Result<(), UnifyError>> {
    let (Elim::App(x, _), init) = sp.split_last()? else { return None };
    // Only where pattern unification can't apply: the last argument is not
    // a bound variable (`?f Int`). Otherwise the failure is real (a
    // variable escaping its scope, say).
    if matches!(x, Val::Neutral(Head::Var(_), s) if s.is_empty()) {
        return None;
    }
    let head = Val::Neutral(Head::Meta(m), Rc::new(init.to_vec()));
    match other {
        Val::Neutral(h @ Head::Var(_), sp2) => {
            let Some((Elim::App(y, _), init2)) = sp2.split_last() else { return Some(Err(UnifyError::NotApplied(m))) };
            Some(unify(g, l, &head, &Val::Neutral(h.clone(), Rc::new(init2.to_vec()))).and_then(|_| unify(g, l, x, y)))
        }
        Val::TyCon(id, args) if !args.is_empty() => {
            let (last, prefix) = args.split_last()?;
            // `\y -> T prefix y`, at level `l`.
            let mut ts: Vec<Tm> = prefix.iter().map(|a| quote(g, l + 1, a)).collect();
            ts.push(Tm::Var(0));
            let lam = Tm::Lam(Rc::from("y"), Mult::Many, Icit::Expl, Rc::new(Tm::TyConApp(*id, ts)));
            let env = (0..l).map(Val::var).collect::<crate::core::Env>();
            let f = eval(g, &env, &lam);
            Some(unify(g, l, &head, &f).and_then(|_| unify(g, l, x, last)))
        }
        Val::TyCon(..) | Val::TupleTy(_) | Val::Pi(..) | Val::Univ(_) => Some(Err(UnifyError::NotApplied(m))),
        Val::Neutral(Head::Def(_), s) if s.is_empty() => Some(Err(UnifyError::NotApplied(m))),
        _ => None,
    }
}
