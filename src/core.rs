//! Core terms, values, normalization by evaluation, and unification (§3–§4).
//!
//! Terms use de Bruijn *indices*; values use de Bruijn *levels* and closures
//! (Kovács' elaboration-zoo design). Metavariables stand for implicit
//! arguments and unknown types; they are solved by pattern unification.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
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
    Str(Rc<str>),
    Bytes(Rc<[u8]>),
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
    Format,
    /// `par t` — identity to the type checker and prover (D34).
    Par,
    Fork,
    Join,
    When,
    /// A stdlib function implemented in Rust (`__builtin`), by qualified name.
    Builtin(Rc<str>),
    /// `forall x y : …, p` (D137): its one argument is a Π over the
    /// variables whose body is the `Bool` (premises implying the
    /// conclusion). Only in specifications; never evaluated or compiled.
    Forall,
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
    Proj(Rc<Tm>, usize),
    /// Record projection: field `index` (counting fields only, not type parameters).
    Field(Rc<Tm>, ConId, usize),
    TyConApp(TyId, Vec<Tm>),
    /// Saturated constructor: type parameters, then fields.
    ConApp(ConId, Vec<Tm>),
    PrimApp(Prim, Vec<Tm>),
    Case(Rc<Tm>, Rc<CaseTm>),
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

pub type Env = Rc<Vec<Val>>;

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
    Prim(Prim, Vec<Val>),
}

#[derive(Clone, Debug)]
pub enum Elim {
    App(Val, Icit),
    Proj(usize),
    Field(ConId, usize),
    Case(Rc<CaseTm>, Env),
}

#[derive(Clone, Debug)]
pub enum Val {
    Neutral(Head, Rc<Vec<Elim>>),
    Lam(Name, Mult, Icit, Closure),
    Pi(Name, Mult, Icit, Rc<Val>, Closure),
    Univ(u32),
    TyCon(TyId, Vec<Val>),
    Con(ConId, Vec<Val>),
    Lit(Lit),
    TupleTy(Vec<Val>),
    Tuple(Vec<Val>),
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
    /// Sealed by its module (D54): does not unfold outside it.
    pub sealed: bool,
    /// Binder positions (over the whole Π-type) that are `comptime` (D59).
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
    /// (for an abstract type: marked `+`, D16).
    pub positive: Vec<bool>,
    /// Per parameter of an abstract type: marked `-`, so it occurs only
    /// negatively (D16).
    pub negative: Vec<bool>,
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
    /// The implicit parameters unknowns stand for, for messages (D141).
    pub meta_origins: RefCell<HashMap<MetaId, MetaOrigin>>,
    /// Remaining δ-unfoldings before evaluation stops unfolding (guards against
    /// non-terminating definitions whose termination isn't checked yet).
    pub fuel: Cell<u64>,
    pub well_known: WellKnown,
}

#[derive(Default, Clone)]
pub struct WellKnown {
    pub bool_ty: Option<TyId>,
    pub true_con: Option<ConId>,
    pub false_con: Option<ConId>,
    /// The prelude's `Nat`, a refinement alias of `Int` (D121).
    pub nat: Option<DefId>,
    pub int: Option<TyId>,
    pub string: Option<TyId>,
    /// `Bytes`, the prelude's alias of `Array U8` (D133).
    pub bytes: Option<DefId>,
    pub array: Option<TyId>,
    /// The prelude's fixed-width aliases and `Char`, with the layout of an
    /// array of them (`checkers_rt::array::Layout`, D133).
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
}

pub const DEFAULT_FUEL: u64 = 200_000;

impl Globals {
    pub fn new() -> Globals {
        Globals {
            defs: Vec::new(),
            tys: Vec::new(),
            cons: Vec::new(),
            metas: RefCell::new(Vec::new()),
            meta_origins: RefCell::new(HashMap::new()),
            fuel: Cell::new(DEFAULT_FUEL),
            well_known: WellKnown::default(),
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
            Some(c) => Val::Con(c, Vec::new()),
            None => Val::Error,
        }
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
    let mut e = (**env).clone();
    e.push(v);
    Rc::new(e)
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
                Val::TyCon(*t, Vec::new())
            } else {
                let tid = *t;
                eval(g, &Rc::new(Vec::new()), &eta(n, &[], |args| Tm::TyConApp(tid, args)))
            }
        }
        Tm::Con(c) => {
            let n = g.arity_con(*c);
            if n == 0 {
                Val::Con(*c, Vec::new())
            } else {
                let cid = *c;
                let icits = con_icits(g, cid);
                eval(g, &Rc::new(Vec::new()), &eta(n, &icits, |args| Tm::ConApp(cid, args)))
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
        Tm::Proj(t, i) => proj(g, eval(g, env, t), *i),
        Tm::Field(t, c, i) => field(g, eval(g, env, t), *c, *i),
        Tm::TyConApp(t, args) => Val::TyCon(*t, args.iter().map(|a| eval(g, env, a)).collect()),
        Tm::ConApp(c, args) => Val::Con(*c, args.iter().map(|a| eval(g, env, a)).collect()),
        Tm::PrimApp(p, args) => prim(g, p, args.iter().map(|a| eval(g, env, a)).collect()),
        Tm::Case(s, c) => case(g, eval(g, env, s), c.clone(), env.clone()),
        Tm::Error => Val::Error,
    }
}

/// Resolve solved metavariables at the head (no δ-unfolding).
pub fn force_meta(g: &Globals, v: Val) -> Val {
    match v {
        Val::Neutral(Head::Meta(m), sp) => match g.meta(m) {
            Some(sol) => {
                let mut r = sol;
                for e in sp.iter() {
                    r = elim(g, r, e.clone());
                }
                force_meta(g, r)
            }
            None => Val::Neutral(Head::Meta(m), sp),
        },
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
    // Fuel bounds unfolding of functions. A type alias can't recurse
    // (cycles are errors, D65), so unfolding it always terminates and costs
    // none: running out of fuel must not stop `U8` from being `Nat`.
    if !is_type_former(&info.ty) {
        if g.fuel.get() == 0 {
            return None;
        }
        g.fuel.set(g.fuel.get() - 1);
    }
    let mut r = eval(g, &Rc::new(Vec::new()), body);
    for e in sp.iter() {
        r = elim(g, r, e.clone());
    }
    Some(r)
}

/// Is this the type of a type (or of a function returning one), as for a
/// type alias?
fn is_type_former(ty: &Tm) -> bool {
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

/// Weak-head normal form: resolve metas and unfold definitions at the head.
/// Is `v` the type `Nat`, or a refinement of it (`U8`, `Char`)? Aliases are
/// unfolded one at a time until `Nat` is met (D121): forcing would go past it
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

/// The layout of an array of `v`, a type (D133): a fixed-width alias's or
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

pub fn force(g: &Globals, v: Val) -> Val {
    let mut v = force_meta(g, v);
    while let Some(u) = unfold(g, &v) {
        v = force_meta(g, u);
    }
    v
}

fn with_elim(h: Head, sp: &Rc<Vec<Elim>>, e: Elim) -> Val {
    let mut s = (**sp).clone();
    s.push(e);
    Val::Neutral(h, Rc::new(s))
}

pub fn elim(g: &Globals, v: Val, e: Elim) -> Val {
    match e {
        Elim::App(a, i) => app(g, v, a, i),
        Elim::Proj(i) => proj(g, v, i),
        Elim::Field(c, i) => field(g, v, c, i),
        Elim::Case(c, env) => case(g, v, c, env),
    }
}

pub fn app(g: &Globals, f: Val, a: Val, i: Icit) -> Val {
    match force_meta(g, f) {
        Val::Lam(_, _, _, c) => apply_closure(g, &c, a),
        Val::Neutral(h, sp) => with_elim(h, &sp, Elim::App(a, i)),
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

fn proj(g: &Globals, v: Val, i: usize) -> Val {
    match force(g, v.clone()) {
        Val::Tuple(vs) => vs.get(i).cloned().unwrap_or(Val::Error),
        f @ Val::Neutral(..) => match stuck_base(g, v, f) {
            Val::Neutral(h, sp) => with_elim(h, &sp, Elim::Proj(i)),
            _ => Val::Error,
        },
        _ => Val::Error,
    }
}

fn field(g: &Globals, v: Val, c: ConId, i: usize) -> Val {
    match force(g, v.clone()) {
        Val::Con(_, args) => {
            let np = g.arity_ty(g.cons[c.0 as usize].ty);
            args.get(np + i).cloned().unwrap_or(Val::Error)
        }
        f @ Val::Neutral(..) => match stuck_base(g, v, f) {
            Val::Neutral(h, sp) => with_elim(h, &sp, Elim::Field(c, i)),
            _ => Val::Error,
        },
        _ => Val::Error,
    }
}

fn case(g: &Globals, v: Val, c: Rc<CaseTm>, env: Env) -> Val {
    match force(g, v.clone()) {
        Val::Con(id, args) => {
            for (cid, n, body) in &c.branches {
                if *cid == id {
                    let fields = &args[args.len() - n..];
                    let mut e = (*env).clone();
                    e.extend(fields.iter().cloned());
                    return eval(g, &Rc::new(e), body);
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
            match &c.default {
                Some(d) => eval(g, &env, d),
                None => Val::Error,
            }
        }
        f @ Val::Neutral(..) => match stuck_base(g, v, f) {
            Val::Neutral(h, sp) => with_elim(h, &sp, Elim::Case(c, env)),
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
    let args: Vec<Val> = orig.iter().map(|a| force_meta(g, a.clone())).collect();
    match prim_value(g, p, &args) {
        Some(v) => v,
        None => Val::Neutral(Head::Prim(p.clone(), args), Rc::new(Vec::new())),
    }
}

fn prim_value(g: &Globals, p: &Prim, args: &[Val]) -> Option<Val> {
    let n2 = || Some((num(&args[0])?, num(&args[1])?));
    let r = match p {
        Prim::Add => n2().and_then(|(a, b)| a.checked_add(b)).map(|n| Val::Lit(Lit::Num(n))),
        // `Sub` carries its operand type: on `Nat`, `a - b` with `a < b` has no value (stuck).
        Prim::Sub => n2().and_then(|(a, b)| {
            let on_nat = args.get(2).is_some_and(|t| is_nat(g, t));
            if on_nat && a < b {
                None
            } else {
                a.checked_sub(b).map(|n| Val::Lit(Lit::Num(n)))
            }
        }),
        Prim::Mul => n2().and_then(|(a, b)| a.checked_mul(b)).map(|n| Val::Lit(Lit::Num(n))),
        Prim::Div => n2().and_then(|(a, b)| a.checked_div_euclid(b)).map(|n| Val::Lit(Lit::Num(n))),
        Prim::Rem => n2().and_then(|(a, b)| a.checked_rem_euclid(b)).map(|n| Val::Lit(Lit::Num(n))),
        Prim::Neg => num(&args[0]).map(|a| Val::Lit(Lit::Num(-a))),
        Prim::Lt => n2().map(|(a, b)| g.bool_val(a < b)),
        Prim::Le => n2().map(|(a, b)| g.bool_val(a <= b)),
        Prim::Gt => n2().map(|(a, b)| g.bool_val(a > b)),
        Prim::Ge => n2().map(|(a, b)| g.bool_val(a >= b)),
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
                    Elim::Proj(i) => Tm::Proj(Rc::new(t), *i),
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
        Val::Error => Tm::Error,
    }
}

fn quote_case(g: &Globals, l: usize, c: &Rc<CaseTm>, env: &Env) -> Rc<CaseTm> {
    let qb = |n: usize, body: &Tm| {
        let mut e = (**env).clone();
        for k in 0..n {
            e.push(Val::var(l + k));
        }
        quote(g, l + n, &eval(g, &Rc::new(e), body))
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
    /// type (`Int`), D141.
    NotApplied(MetaId),
}

/// What an unknown stands for (D141): the implicit parameter `name` of
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
    for (dom, e) in sp.iter().enumerate() {
        match e {
            Elim::App(a, i) => match force(g, a.clone()) {
                Val::Neutral(Head::Var(x), s) if s.is_empty() && !ren.contains_key(&x) => {
                    ren.insert(x, dom);
                    icits.push(*i);
                }
                _ => return Err(UnifyError::Mismatch),
            },
            _ => return Err(UnifyError::Mismatch),
        }
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
                Elim::Proj(i) => Tm::Proj(Rc::new(t), *i),
                Elim::Field(c, i) => Tm::Field(Rc::new(t), *c, *i),
                Elim::Case(c, env) => Tm::Case(Rc::new(t), rename_case(g, m, p, c, env)?),
            };
        }
        Ok(t)
    };
    match force_meta(g, v.clone()) {
        Val::Neutral(Head::Meta(m2), sp) => {
            if m2 == m {
                return Err(UnifyError::Mismatch); // occurs check
            }
            go_sp(Tm::Meta(m2), &sp)
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
        Val::Error => Ok(Tm::Error),
    }
}

fn rename_case(g: &Globals, m: MetaId, p: &PartialRenaming, c: &Rc<CaseTm>, env: &Env) -> Result<Rc<CaseTm>, UnifyError> {
    let rb = |n: usize, body: &Tm| -> Result<Tm, UnifyError> {
        let mut e = (**env).clone();
        let mut pr = PartialRenaming { dom: p.dom, cod: p.cod, ren: p.ren.clone() };
        for _ in 0..n {
            e.push(Val::var(pr.cod));
            pr = lift(&pr);
        }
        rename(g, m, &pr, &eval(g, &Rc::new(e), body))
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
    let sol = eval(g, &Rc::new(Vec::new()), &t);
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
            (Elim::Proj(i), Elim::Proj(j)) if i == j => {}
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

pub fn unify(g: &Globals, l: usize, a: &Val, b: &Val) -> Result<(), UnifyError> {
    let a = force_meta(g, a.clone());
    let b = force_meta(g, b.clone());
    let r = unify_whnf(g, l, &a, &b);
    if r.is_ok() {
        return r;
    }
    // Retry after unfolding a definition at either head.
    if let Some(a2) = unfold(g, &a) {
        return unify(g, l, &a2, &b);
    }
    if let Some(b2) = unfold(g, &b) {
        return unify(g, l, &a, &b2);
    }
    r
}

fn unify_whnf(g: &Globals, l: usize, a: &Val, b: &Val) -> Result<(), UnifyError> {
    match (a, b) {
        (Val::Error, _) | (_, Val::Error) => Ok(()),
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
        (Val::TyCon(t1, a1), Val::TyCon(t2, a2)) if t1 == t2 => unify_many(g, l, a1, a2),
        (Val::Con(c1, a1), Val::Con(c2, a2)) if c1 == c2 => unify_many(g, l, a1, a2),
        (Val::Lit(x), Val::Lit(y)) if x == y => Ok(()),
        (Val::TupleTy(x), Val::TupleTy(y)) => unify_many(g, l, x, y),
        (Val::Tuple(x), Val::Tuple(y)) => unify_many(g, l, x, y),
        (Val::Neutral(Head::Meta(m1), s1), Val::Neutral(Head::Meta(m2), s2)) if m1 == m2 => unify_sp(g, l, s1, s2),
        (Val::Neutral(Head::Meta(m1), s1), Val::Neutral(Head::Meta(m2), s2)) => {
            // Solve the meta with the larger scope first; fall back to the other.
            if s1.len() >= s2.len() {
                solve(g, l, *m1, s1, b).or_else(|_| solve(g, l, *m2, s2, a))
            } else {
                solve(g, l, *m2, s2, a).or_else(|_| solve(g, l, *m1, s1, b))
            }
        }
        (Val::Neutral(Head::Meta(m), sp), other) | (other, Val::Neutral(Head::Meta(m), sp)) => {
            solve(g, l, *m, sp, other).or_else(|e| first_order(g, l, *m, sp, other).unwrap_or(Err(e)))
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

/// Render a core term for error messages. `names` are the local variable
/// names, innermost last.
pub fn show(g: &Globals, names: &[Name], t: &Tm) -> String {
    let mut ns: Vec<Name> = names.to_vec();
    show_prec(g, &mut ns, t, 0)
}

fn fresh(ns: &[Name], x: &Name) -> Name {
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

fn paren(b: bool, s: String) -> String {
    if b {
        format!("({s})")
    } else {
        s
    }
}

fn show_prec(g: &Globals, ns: &mut Vec<Name>, t: &Tm, p: u8) -> String {
    match t {
        Tm::Var(i) => ns.get(ns.len().wrapping_sub(1 + i)).map(|n| n.to_string()).unwrap_or_else(|| format!("#{i}")),
        Tm::Def(d) => g.defs[d.0 as usize].name.to_string(),
        Tm::TyCon(t) => g.tys[t.0 as usize].name.to_string(),
        Tm::Con(c) => g.cons[c.0 as usize].name.to_string(),
        Tm::Meta(m) => match g.meta(*m) {
            Some(v) => show_prec(g, ns, &quote(g, ns.len(), &v), p),
            // An unknown the checker has not worked out yet: by the
            // parameter it stands for (D141), else `_`.
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
            // An inline refinement (D82) prints as written.
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
        Tm::Lit(Lit::Num(n)) => n.to_string(),
        Tm::Lit(Lit::Str(s)) => format!("{s:?}"),
        Tm::Lit(Lit::Bytes(b)) => format!("b{:?}", String::from_utf8_lossy(b)),
        Tm::TupleTy(ts) if ts.is_empty() => "Unit".into(),
        Tm::TupleTy(ts) | Tm::Tuple(ts) => {
            format!("({})", ts.iter().map(|x| show_prec(g, ns, x, 0)).collect::<Vec<_>>().join(", "))
        }
        Tm::Proj(x, i) => format!("{}.{i}", show_prec(g, ns, x, 2)),
        Tm::Field(x, c, i) => {
            let f = &g.cons[c.0 as usize].fields[*i].0;
            format!("{}.{f}", show_prec(g, ns, x, 2))
        }
        Tm::TyConApp(ty, args) => {
            let ti = &g.tys[ty.0 as usize];
            if args.is_empty() {
                return ti.name.to_string();
            }
            let s = format!(
                "{} {}",
                ti.name,
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
                return ci.name.to_string();
            }
            let s = format!(
                "{} {}",
                ci.name,
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
                    if let (Prim::Neg, [a]) = (pr, args.as_slice()) {
                        return format!("-{}", show_prec(g, ns, a, 2));
                    }
                    if let (Prim::Index, [a, i, ..]) = (pr, args.as_slice()) {
                        return format!("{}[{}]", show_prec(g, ns, a, 3), show_prec(g, ns, i, 0));
                    }
                    let name = match pr {
                        Prim::Builtin(n) => n.to_string(),
                        Prim::Len => "len".into(),
                        Prim::Format => "format".into(),
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
        Tm::Case(s, c) => {
            // `if` (and `and`/`or`) are matches on `Bool`.
            let wk = &g.well_known;
            let arm = |con: Option<ConId>| c.branches.iter().find(|b| Some(b.0) == con).map(|b| &b.2);
            if let (Some(t), Some(f), 2) = (arm(wk.true_con), arm(wk.false_con), c.branches.len()) {
                let (cs, ts, fs) = (show_prec(g, ns, s, 0), show_prec(g, ns, t, 0), show_prec(g, ns, f, 0));
                let text = match (ts.as_str(), fs.as_str()) {
                    (_, "False") => format!("{cs} and {ts}"),
                    ("True", _) => format!("{cs} or {fs}"),
                    _ => format!("if {cs} then {ts} else {fs}"),
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
    let mut go = |x: &Tm, d: usize| free_vars(x, d, out);
    match t {
        Tm::Var(i) if *i >= depth => {
            out.insert(i - depth);
        }
        Tm::Pi(_, _, _, a, b) => {
            go(a, depth);
            go(b, depth + 1);
        }
        Tm::Lam(_, _, _, b) => go(b, depth + 1),
        Tm::App(f, a, _, _) => {
            go(f, depth);
            go(a, depth);
        }
        Tm::Let(_, _, ty, v, b) => {
            go(ty, depth);
            go(v, depth);
            go(b, depth + 1);
        }
        Tm::TyConApp(_, v) | Tm::TupleTy(v) | Tm::ConApp(_, v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => {
            for x in v {
                go(x, depth);
            }
        }
        Tm::Proj(x, _) | Tm::Field(x, _, _) => go(x, depth),
        Tm::Case(s, c) => {
            go(s, depth);
            for (_, n, b) in &c.branches {
                go(b, depth + n);
            }
            for (_, b) in &c.lits {
                go(b, depth);
            }
            if let Some(b) = &c.default {
                go(b, depth);
            }
        }
        _ => {}
    }
}

/// `t` with each free variable `i` (an index from outside `depth` binders)
/// replaced by `f(i)`.
pub fn rename_free(t: &Tm, depth: usize, f: &dyn Fn(usize) -> usize) -> Tm {
    let go = |x: &Tm, d: usize| rename_free(x, d, f);
    let rc = |x: &Rc<Tm>, d: usize| Rc::new(rename_free(x, d, f));
    let all = |v: &Vec<Tm>| v.iter().map(|x| go(x, depth)).collect::<Vec<_>>();
    match t {
        Tm::Var(i) if *i >= depth => Tm::Var(f(i - depth) + depth),
        Tm::Pi(x, m, i, a, b) => Tm::Pi(x.clone(), *m, *i, rc(a, depth), rc(b, depth + 1)),
        Tm::Lam(x, m, i, b) => Tm::Lam(x.clone(), *m, *i, rc(b, depth + 1)),
        Tm::App(a, b, i, m) => Tm::App(rc(a, depth), rc(b, depth), *i, *m),
        Tm::Let(x, m, ty, v, b) => Tm::Let(x.clone(), *m, rc(ty, depth), rc(v, depth), rc(b, depth + 1)),
        Tm::TyConApp(c, v) => Tm::TyConApp(*c, all(v)),
        Tm::TupleTy(v) => Tm::TupleTy(all(v)),
        Tm::ConApp(c, v) => Tm::ConApp(*c, all(v)),
        Tm::Tuple(v) => Tm::Tuple(all(v)),
        Tm::PrimApp(p, v) => Tm::PrimApp(p.clone(), all(v)),
        Tm::Proj(x, i) => Tm::Proj(rc(x, depth), *i),
        Tm::Field(x, c, i) => Tm::Field(rc(x, depth), *c, *i),
        Tm::Case(s, c) => Tm::Case(
            rc(s, depth),
            Rc::new(CaseTm {
                branches: c.branches.iter().map(|(k, n, b)| (*k, *n, go(b, depth + n))).collect(),
                lits: c.lits.iter().map(|(l, b)| (l.clone(), go(b, depth))).collect(),
                default: c.default.as_ref().map(|b| go(b, depth)),
            }),
        ),
        other => other.clone(),
    }
}

/// An inline refinement `(n~Int, n >= 5)` (D82): an alias with no name of
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
        let mut h = t;
        while let Tm::App(f, ..) = h {
            h = f;
        }
        if let Tm::Meta(m) = h {
            if g.meta(*m).is_some() {
                let env = Rc::new((0..l).map(Val::var).collect::<Vec<_>>());
                return Some(fix_mults(g, &quote(g, l, &eval(g, &env, t))));
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
            Tm::Proj(x, i) => rc(x, 0).map(|nx| Tm::Proj(nx, *i)),
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
            let env = Rc::new((0..l).map(Val::var).collect::<Vec<_>>());
            let f = eval(g, &env, &lam);
            Some(unify(g, l, &head, &f).and_then(|_| unify(g, l, x, last)))
        }
        Val::TyCon(..) | Val::TupleTy(_) | Val::Pi(..) | Val::Univ(_) => Some(Err(UnifyError::NotApplied(m))),
        Val::Neutral(Head::Def(_), s) if s.is_empty() => Some(Err(UnifyError::NotApplied(m))),
        _ => None,
    }
}
