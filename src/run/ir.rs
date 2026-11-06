//! Erasure (§13.1): core terms → runtime code. Types, implicit and `ghost`
//! arguments become `Erased`; everything else keeps its shape (de Bruijn
//! indices included), so the evaluator can follow the core term exactly.

use super::num::Num;
use super::value::Value;
use crate::core::{eval, force, CaseTm, ConId, DefId, Globals, Lit, Mult, Prim, Tm, Val};
use std::sync::Arc;

pub enum Ir {
    Var(usize),
    Global(DefId),
    Erased,
    Lit(Value),
    Lam(Option<DefId>, Arc<Ir>),
    /// A call: head and arguments, flattened from nested applications.
    Call(Arc<Ir>, Vec<Arc<Ir>>),
    Let(Arc<Ir>, Arc<Ir>),
    Tuple(Vec<Arc<Ir>>),
    Proj(Arc<Ir>, usize),
    Field(Arc<Ir>, usize),
    /// Saturated constructor: fields only.
    Con(ConId, Vec<Arc<Ir>>),
    /// A constructor used as a function.
    ConFn(ConId),
    /// A primitive; the flag marks `Nat` subtraction (checked, D41).
    Prim(Op, Vec<Arc<Ir>>, bool),
    /// `par (e1, …, en)`: the components, evaluated in parallel (D69).
    Par(Vec<Arc<Ir>>),
    Case(Arc<Ir>, Arc<IrCase>),
    /// Code the type checker reported an error for; never reached in a checked program.
    Fail(&'static str),
}

/// A primitive operation at run time (`Prim` without the type checker's
/// builtin names, so that code can be shared between threads).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
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
    Par,
    Fork,
    Join,
    When,
}

impl Op {
    pub fn of(p: &Prim) -> Option<Op> {
        Some(match p {
            Prim::Add => Op::Add,
            Prim::Sub => Op::Sub,
            Prim::Mul => Op::Mul,
            Prim::Div => Op::Div,
            Prim::Rem => Op::Rem,
            Prim::Neg => Op::Neg,
            Prim::Eq => Op::Eq,
            Prim::Ne => Op::Ne,
            Prim::Lt => Op::Lt,
            Prim::Le => Op::Le,
            Prim::Gt => Op::Gt,
            Prim::Ge => Op::Ge,
            Prim::Concat => Op::Concat,
            Prim::Len => Op::Len,
            Prim::Index => Op::Index,
            Prim::Format => Op::Format,
            Prim::Par => Op::Par,
            Prim::Fork => Op::Fork,
            Prim::Join => Op::Join,
            Prim::When => Op::When,
            Prim::Builtin(_) => return None,
        })
    }
}

pub struct IrCase {
    pub branches: Vec<(ConId, usize, Arc<Ir>)>,
    pub lits: Vec<(Value, Arc<Ir>)>,
    pub default: Option<Arc<Ir>>,
}

pub fn lit_value(l: &Lit) -> Value {
    match l {
        Lit::Num(n) => Value::Num(Num::S(*n)),
        Lit::Str(s) => Value::Str(Arc::from(&**s)),
        Lit::Bytes(b) => Value::Bytes(Arc::from(&**b)),
    }
}

pub struct Compiler<'g> {
    pub g: &'g Globals,
    pub owner: Option<DefId>,
}

impl Compiler<'_> {
    pub fn compile(&self, t: &Tm) -> Arc<Ir> {
        Arc::new(self.go(t))
    }

    fn go(&self, t: &Tm) -> Ir {
        match t {
            Tm::Var(i) => Ir::Var(*i),
            Tm::Def(d) => Ir::Global(*d),
            Tm::Con(c) => Ir::ConFn(*c),
            Tm::TyCon(_) | Tm::Univ(_) | Tm::Pi(..) | Tm::TupleTy(_) | Tm::TyConApp(..) | Tm::Meta(_) => Ir::Erased,
            Tm::Lam(_, _, _, b) => Ir::Lam(self.owner, self.compile(b)),
            Tm::App(..) => {
                let mut args = Vec::new();
                let mut h = t;
                while let Tm::App(f, a, _, m) = h {
                    args.push(if *m == Mult::Zero { Arc::new(Ir::Erased) } else { self.compile(a) });
                    h = f;
                }
                args.reverse();
                // A constructor with all its arguments is built directly.
                if let Tm::Con(c) = h {
                    if args.len() == self.g.arity_con(*c) {
                        let ci = &self.g.cons[c.0 as usize];
                        let np = self.g.arity_ty(ci.ty);
                        let fields = args
                            .into_iter()
                            .skip(np)
                            .zip(&ci.fields)
                            .map(|(a, f)| if f.1 == Mult::Zero { Arc::new(Ir::Erased) } else { a })
                            .collect();
                        return Ir::Con(*c, fields);
                    }
                }
                Ir::Call(self.compile(h), args)
            }
            Tm::Let(_, m, _, v, b) => {
                let v = if *m == Mult::Zero { Arc::new(Ir::Erased) } else { self.compile(v) };
                Ir::Let(v, self.compile(b))
            }
            Tm::Lit(l) => Ir::Lit(lit_value(l)),
            Tm::Tuple(xs) => Ir::Tuple(xs.iter().map(|x| self.compile(x)).collect()),
            Tm::Proj(x, i) => Ir::Proj(self.compile(x), *i),
            Tm::Field(x, _, i) => Ir::Field(self.compile(x), *i),
            Tm::ConApp(c, args) => {
                let ci = &self.g.cons[c.0 as usize];
                let np = self.g.arity_ty(ci.ty);
                let fields = args[np..]
                    .iter()
                    .zip(&ci.fields)
                    .map(|(a, f)| if f.1 == Mult::Zero { Arc::new(Ir::Erased) } else { self.compile(a) })
                    .collect();
                Ir::Con(*c, fields)
            }
            Tm::PrimApp(p, args) => {
                if let (Prim::Par, [Tm::Tuple(xs)]) = (p, &args[..]) {
                    return Ir::Par(xs.iter().map(|x| self.compile(x)).collect());
                }
                let nat = *p == Prim::Sub && args.get(2).is_some_and(|ty| self.is_nat(ty));
                let n = if *p == Prim::Sub { 2 } else { args.len() };
                match Op::of(p) {
                    Some(op) => Ir::Prim(op, args.iter().take(n).map(|a| self.compile(a)).collect(), nat),
                    None => Ir::Fail("an unexpected primitive"),
                }
            }
            Tm::Case(s, c) => Ir::Case(self.compile(s), Arc::new(self.case(c))),
            Tm::Error => Ir::Fail("code with a type error"),
        }
    }

    fn case(&self, c: &CaseTm) -> IrCase {
        IrCase {
            branches: c.branches.iter().map(|(con, n, b)| (*con, *n, self.compile(b))).collect(),
            lits: c.lits.iter().map(|(l, b)| (lit_value(l), self.compile(b))).collect(),
            default: c.default.as_ref().map(|d| self.compile(d)),
        }
    }

    /// Is this type term `Nat`? It may mention local variables and solved metas.
    fn is_nat(&self, ty: &Tm) -> bool {
        let depth = max_var(ty).map_or(0, |m| m + 1);
        let env = std::rc::Rc::new((0..depth).map(Val::var).collect::<Vec<_>>());
        matches!(force(self.g, eval(self.g, &env, ty)), Val::TyCon(t, _) if Some(t) == self.g.well_known.nat)
    }
}

fn max_var(t: &Tm) -> Option<usize> {
    let m = |a: Option<usize>, b: Option<usize>| a.max(b);
    match t {
        Tm::Var(i) => Some(*i),
        Tm::App(f, a, ..) => m(max_var(f), max_var(a)),
        Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => {
            v.iter().map(max_var).fold(None, m)
        }
        Tm::Proj(x, _) | Tm::Field(x, _, _) => max_var(x),
        // Binders shift indices; types under binders are not expected here.
        Tm::Pi(_, _, _, a, b) => m(max_var(a), max_var(b).and_then(|x| x.checked_sub(1))),
        Tm::Lam(_, _, _, b) => max_var(b).and_then(|x| x.checked_sub(1)),
        _ => None,
    }
}

/// A copy of `ir` that shares no node with it. Each thread runs its own copy
/// of a function's code, so evaluating it doesn't make threads contend on
/// the reference counts of shared nodes (M7).
pub fn private(ir: &Ir) -> Arc<Ir> {
    let all = |xs: &[Arc<Ir>]| xs.iter().map(|x| private(x)).collect::<Vec<_>>();
    Arc::new(match ir {
        Ir::Var(i) => Ir::Var(*i),
        Ir::Global(d) => Ir::Global(*d),
        Ir::Erased => Ir::Erased,
        Ir::Lit(v) => Ir::Lit(private_lit(v)),
        Ir::Lam(o, b) => Ir::Lam(*o, private(b)),
        Ir::Call(h, xs) => Ir::Call(private(h), all(xs)),
        Ir::Let(v, b) => Ir::Let(private(v), private(b)),
        Ir::Tuple(xs) => Ir::Tuple(all(xs)),
        Ir::Proj(x, i) => Ir::Proj(private(x), *i),
        Ir::Field(x, i) => Ir::Field(private(x), *i),
        Ir::Con(c, xs) => Ir::Con(*c, all(xs)),
        Ir::ConFn(c) => Ir::ConFn(*c),
        Ir::Prim(op, xs, nat) => Ir::Prim(*op, all(xs), *nat),
        Ir::Par(xs) => Ir::Par(all(xs)),
        Ir::Case(s, c) => Ir::Case(
            private(s),
            Arc::new(IrCase {
                branches: c.branches.iter().map(|(k, n, b)| (*k, *n, private(b))).collect(),
                lits: c.lits.iter().map(|(v, b)| (private_lit(v), private(b))).collect(),
                default: c.default.as_ref().map(|b| private(b)),
            }),
        ),
        Ir::Fail(m) => Ir::Fail(m),
    })
}

fn private_lit(v: &Value) -> Value {
    match v {
        Value::Str(s) => Value::Str(Arc::from(&**s)),
        Value::Bytes(b) => Value::Bytes(Arc::from(&**b)),
        other => other.clone(),
    }
}
