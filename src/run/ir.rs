//! Erasure (§13.1): core terms → runtime code. Types, implicit and `ghost`
//! arguments become `Erased`; everything else keeps its shape (de Bruijn
//! indices included), so the evaluator can follow the core term exactly.

use super::num::Num;
use super::value::Value;
use crate::core::{eval, force, CaseTm, ConId, DefId, Globals, Lit, Mult, Prim, Tm, Val};
use std::rc::Rc;

pub enum Ir {
    Var(usize),
    Global(DefId),
    Erased,
    Lit(Value),
    Lam(Option<DefId>, Rc<Ir>),
    /// A call: head and arguments, flattened from nested applications.
    Call(Rc<Ir>, Vec<Rc<Ir>>),
    Let(Rc<Ir>, Rc<Ir>),
    Tuple(Vec<Rc<Ir>>),
    Proj(Rc<Ir>, usize),
    Field(Rc<Ir>, usize),
    /// Saturated constructor: fields only.
    Con(ConId, Vec<Rc<Ir>>),
    /// A constructor used as a function.
    ConFn(ConId),
    /// A primitive; the flag marks `Nat` subtraction (checked, D41).
    Prim(Prim, Vec<Rc<Ir>>, bool),
    Case(Rc<Ir>, Rc<IrCase>),
    /// Code the type checker reported an error for; never reached in a checked program.
    Fail(&'static str),
}

pub struct IrCase {
    pub branches: Vec<(ConId, usize, Rc<Ir>)>,
    pub lits: Vec<(Value, Rc<Ir>)>,
    pub default: Option<Rc<Ir>>,
}

pub fn lit_value(l: &Lit) -> Value {
    match l {
        Lit::Num(n) => Value::Num(Num::S(*n)),
        Lit::Str(s) => Value::Str(s.clone()),
        Lit::Bytes(b) => Value::Bytes(b.clone()),
    }
}

pub struct Compiler<'g> {
    pub g: &'g Globals,
    pub owner: Option<DefId>,
}

impl Compiler<'_> {
    pub fn compile(&self, t: &Tm) -> Rc<Ir> {
        Rc::new(self.go(t))
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
                    args.push(if *m == Mult::Zero { Rc::new(Ir::Erased) } else { self.compile(a) });
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
                            .map(|(a, f)| if f.1 == Mult::Zero { Rc::new(Ir::Erased) } else { a })
                            .collect();
                        return Ir::Con(*c, fields);
                    }
                }
                Ir::Call(self.compile(h), args)
            }
            Tm::Let(_, m, _, v, b) => {
                let v = if *m == Mult::Zero { Rc::new(Ir::Erased) } else { self.compile(v) };
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
                    .map(|(a, f)| if f.1 == Mult::Zero { Rc::new(Ir::Erased) } else { self.compile(a) })
                    .collect();
                Ir::Con(*c, fields)
            }
            Tm::PrimApp(p, args) => {
                let nat = *p == Prim::Sub && args.get(2).is_some_and(|ty| self.is_nat(ty));
                let n = if *p == Prim::Sub { 2 } else { args.len() };
                Ir::Prim(p.clone(), args.iter().take(n).map(|a| self.compile(a)).collect(), nat)
            }
            Tm::Case(s, c) => Ir::Case(self.compile(s), Rc::new(self.case(c))),
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
        let env = Rc::new((0..depth).map(Val::var).collect::<Vec<_>>());
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
