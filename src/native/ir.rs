//! Erasure (§13.1): core terms → runtime code. Types, implicit and `ghost`
//! arguments become `Erased`; everything else keeps its shape (de Bruijn
//! indices included). Closure conversion (`lower`) starts from here.

use crate::core::{eval, CaseTm, ConId, DefId, Globals, Mult, Prim, Tm, Val};
use std::sync::Arc;

/// A literal at run time.
#[derive(Clone)]
pub enum Lit {
    Num(i128),
    Str(Arc<str>),
    Bytes(Arc<[u8]>),
}

pub enum Ir {
    Var(usize),
    Global(DefId),
    Erased,
    Lit(Lit),
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
    /// A primitive; the flag marks `Nat` subtraction (checked, D41), or
    /// indexing an `Array U8` (a bytes object, D133).
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
    pub lits: Vec<(Lit, Arc<Ir>)>,
    pub default: Option<Arc<Ir>>,
}

pub fn lit_value(l: &crate::core::Lit) -> Lit {
    match l {
        crate::core::Lit::Num(n) => Lit::Num(*n),
        crate::core::Lit::Str(s) => Lit::Str(Arc::from(&**s)),
        crate::core::Lit::Bytes(b) => Lit::Bytes(Arc::from(&**b)),
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
                    args.push(if *m == Mult::Zero { Arc::new(self.erased(a)) } else { self.compile(a) });
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
                // The flag: `Nat` subtraction (checked), or indexing an
                // `Array U8`, always a bytes object (D133).
                let nat = match p {
                    Prim::Sub => args.get(2).is_some_and(|ty| self.is_nat(ty)),
                    Prim::Index => args.get(2).is_some_and(|ty| self.is_bytes_elem(ty)),
                    _ => false,
                };
                let n = if matches!(p, Prim::Sub | Prim::Index) { 2 } else { args.len() };
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

    /// An erased argument. A type is passed as its layout word (D133): an
    /// array of it is laid out by that word; anything else as nothing.
    fn erased(&self, a: &Tm) -> Ir {
        let mut h = a;
        while let Tm::App(f, ..) = h {
            h = f;
        }
        let typelike = match h {
            Tm::Var(_) | Tm::Meta(_) | Tm::TyCon(_) | Tm::TyConApp(..) => true,
            Tm::Def(d) => self.g.defs.get(d.0 as usize).is_some_and(|i| matches!(i.ty, Tm::Univ(_))),
            _ => false,
        };
        if !typelike {
            return Ir::Erased;
        }
        let depth = max_var(a).map_or(0, |m| m + 1);
        let env = std::rc::Rc::new((0..depth).map(Val::var).collect::<Vec<_>>());
        match crate::core::layout_of(self.g, &eval(self.g, &env, a)) {
            Ok(0) => Ir::Erased,
            Ok(l) => Ir::Lit(Lit::Num(l as i128)),
            Err(level) if level < depth => Ir::Var(depth - 1 - level),
            Err(_) => Ir::Erased,
        }
    }

    /// Is this element type `U8`, so the array is a bytes object (D133)?
    fn is_bytes_elem(&self, ty: &Tm) -> bool {
        let depth = max_var(ty).map_or(0, |m| m + 1);
        let env = std::rc::Rc::new((0..depth).map(Val::var).collect::<Vec<_>>());
        crate::core::layout_of(self.g, &eval(self.g, &env, ty)) == Ok(checkers_rt::array::Layout::U8 as u8)
    }

    /// Is this type term `Nat`? It may mention local variables and solved metas.
    fn is_nat(&self, ty: &Tm) -> bool {
        let depth = max_var(ty).map_or(0, |m| m + 1);
        let env = std::rc::Rc::new((0..depth).map(Val::var).collect::<Vec<_>>());
        crate::core::is_nat(self.g, &eval(self.g, &env, ty))
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

/// The body to run for `d`: staged, generated (numbered after `g.defs`), or
/// elaborated.
pub fn body_of(g: &Globals, staged: Option<&crate::stage::Staged>, d: DefId) -> Option<Tm> {
    let n = g.defs.len();
    if let Some(s) = staged {
        if (d.0 as usize) >= n {
            return s.extra.get(d.0 as usize - n).map(|e| e.1.clone());
        }
        if let Some(b) = s.bodies.get(&d) {
            return Some(b.clone());
        }
    }
    g.defs.get(d.0 as usize).and_then(|i| i.body.clone())
}

/// The definitions code refers to.
pub fn globals_in(ir: &Ir, out: &mut Vec<DefId>) {
    match ir {
        Ir::Global(d) => out.push(*d),
        Ir::Lam(_, b) => globals_in(b, out),
        Ir::Call(h, xs) => {
            globals_in(h, out);
            xs.iter().for_each(|x| globals_in(x, out));
        }
        Ir::Let(a, b) => {
            globals_in(a, out);
            globals_in(b, out);
        }
        Ir::Tuple(xs) | Ir::Con(_, xs) | Ir::Prim(_, xs, _) | Ir::Par(xs) => xs.iter().for_each(|x| globals_in(x, out)),
        Ir::Proj(x, _) | Ir::Field(x, _) => globals_in(x, out),
        Ir::Case(s, c) => {
            globals_in(s, out);
            c.branches.iter().for_each(|(_, _, b)| globals_in(b, out));
            c.lits.iter().for_each(|(_, b)| globals_in(b, out));
            if let Some(d) = &c.default {
                globals_in(d, out);
            }
        }
        _ => {}
    }
}
