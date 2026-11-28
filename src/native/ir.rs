//! Erasure (§13.1): core terms → runtime code. Types, implicit and `ghost`
//! arguments become `Erased`; everything else keeps its shape (de Bruijn
//! indices included). Closure conversion (`lower`) starts from here.

use crate::core::{eval, max_var, CaseTm, ConId, DefId, Elim, Globals, Head, Icit, Mult, Prim, Tm, Val};
use std::rc::Rc;
use std::sync::Arc;

/// A literal at run time.
#[derive(Clone)]
pub enum Lit {
    Num(i128),
    /// An integer outside `i128`'s range, in decimal.
    Big(Arc<str>),
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
    /// Component `i`; with the flag, and the rest after it (#673).
    Proj(Arc<Ir>, usize, bool),
    Field(Arc<Ir>, usize),
    /// Saturated constructor: fields only.
    Con(ConId, Vec<Arc<Ir>>),
    /// A constructor used as a function.
    ConFn(ConId),
    /// A primitive; the flag marks `Nat` subtraction (checked, #536), or
    /// indexing an `Array U8` (a bytes object, #624).
    Prim(Op, Vec<Arc<Ir>>, bool),
    /// `par (e1, …, en)`: the components, evaluated in parallel (#562).
    Par(Vec<Arc<Ir>>),
    Case(Arc<Ir>, Arc<IrCase>),
    /// Code of definition `d` (or of none) placed in another's by an
    /// optimization (`inline`): a runtime error in it names `d`.
    At(Option<DefId>, Arc<Ir>),
    /// Code the type checker reported an error for; never reached in a checked program.
    Fail(&'static str),
    /// A value known when the program is compiled (§8.9), laid out as it is
    /// at run time: a node of static data.
    Static(Arc<super::lower::Static>, u32),
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
    Par,
    When,
    /// A type constructor's descriptor applied to one more argument's (#170).
    TypeApply,
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
            Prim::Par => Op::Par,
            Prim::When => Op::When,
            Prim::Builtin(_) | Prim::Forall | Prim::Effect(_) => return None,
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
        crate::core::Lit::Big(n) => Lit::Big(Arc::from(n.to_string())),
        crate::core::Lit::Str(s) => Lit::Str(Arc::from(&**s)),
        crate::core::Lit::Bytes(b) => Lit::Bytes(Arc::from(&**b)),
    }
}

pub struct Compiler<'g> {
    pub g: &'g Globals,
    pub owner: Option<DefId>,
    /// Where calls passing known instances' dictionaries get specialized
    /// copies (`spec`); `None`: nowhere.
    pub spec: Option<super::spec::SpecCx<'g>>,
    /// The functions known to be bound to the variables in scope: one entry
    /// per binder the code being compiled is under (`spec`).
    fns: super::spec::Fns,
}

impl<'g> Compiler<'g> {
    /// Erasure without specialization.
    pub fn new(g: &'g Globals, owner: Option<DefId>) -> Self {
        Compiler { g, owner, spec: None, fns: Default::default() }
    }

    /// Erasure with specialization, in `spec`.
    pub fn specializing(g: &'g Globals, owner: Option<DefId>, spec: super::spec::SpecCx<'g>) -> Self {
        Compiler { g, owner, spec: Some(spec), fns: Default::default() }
    }

    /// This compiler, for code under `n` more binders.
    fn under(&self, n: usize) -> Compiler<'g> {
        let mut fns = self.fns.clone();
        fns.extend(std::iter::repeat_n(None, n));
        Compiler { fns, ..*self }
    }

    /// This compiler, for code under one more binder, bound to the known
    /// function `f`.
    fn knowing(&self, f: &Rc<super::spec::Bound>) -> Compiler<'g> {
        let mut fns = self.fns.clone();
        fns.push(Some(f.clone()));
        Compiler { fns, ..*self }
    }

    /// Variable `i`, as a value: if it is bound to a known function, its
    /// closure is built.
    fn var(&self, i: usize) -> Ir {
        if let Some(Some(b)) = self.fns.len().checked_sub(i + 1).and_then(|l| self.fns.get(l)) {
            b.used.set(true);
        }
        Ir::Var(i)
    }

    /// `t` with its variables bound to known functions marked as such
    /// (`spec::know`), if it is small enough to be put into a copy or a
    /// `let`'s body: where it is called, passed, or bound. A larger term's
    /// variables are marked as its parts are compiled.
    fn know(&self, t: &Rc<Tm>) -> Rc<Tm> {
        if self.fns.is_empty() || !super::spec::small(t) {
            return t.clone();
        }
        Rc::new(super::spec::know(t, &self.fns, 0))
    }

    pub fn compile(&self, t: &Tm) -> Arc<Ir> {
        Arc::new(self.go(t))
    }

    pub fn go_pub(&self, t: &Tm) -> Ir {
        self.go(t)
    }

    fn go(&self, t: &Tm) -> Ir {
        match t {
            Tm::Var(i) => self.var(*i),
            // A constant known at compile time is its value (§8.9).
            Tm::Def(d) => match crate::core::known_const(self.g, *d) {
                Some(v) => self.go(&v),
                None => Ir::Global(self.reported(*d)),
            },
            // A constructor stored as its one kept field (#170), used as a
            // function: it returns that argument.
            Tm::Con(c) => match self.g.unboxed_field(*c) {
                Some(k) => {
                    let np = self.g.arity_ty(self.g.cons[c.0 as usize].ty);
                    let n = self.g.arity_con(*c);
                    let body = if self.g.is_dict_type_field(*c, k) { Ir::Erased } else { Ir::Var(n - 1 - np - k) };
                    (0..n).fold(body, |b, _| Ir::Lam(self.owner, Arc::new(b)))
                }
                None => Ir::ConFn(*c),
            },
            Tm::TyCon(_) | Tm::Univ(_) | Tm::Pi(..) | Tm::TupleTy(_) | Tm::TyConApp(..) | Tm::Meta(_) => Ir::Erased,
            Tm::Lam(_, _, _, b) => Ir::Lam(self.owner, self.under(1).compile(b)),
            Tm::App(..) => {
                if let Some(direct) = known_instance(self.g, t) {
                    return self.go(&direct);
                }
                let mut known = Vec::new();
                let mut h = t;
                while let Tm::App(f, a, _, m) = h {
                    known.push((self.know(a), *m));
                    h = f;
                }
                known.reverse();
                let spine: Vec<(&Rc<Tm>, Mult)> = known.iter().map(|(a, m)| (a, *m)).collect();
                let head = match h {
                    Tm::Var(_) => super::spec::know(h, &self.fns, 0),
                    _ => h.clone(),
                };
                let h = &head;
                // A variable bound to a known function, called: the
                // function, called directly.
                if let Some((_, f)) = super::spec::known_var(h) {
                    let call = spine.iter().fold((*f).clone(), |c, (a, m)| Tm::App(Rc::new(c), (*a).clone(), Icit::Expl, *m));
                    return self.go(&call);
                }
                // Code of another definition applied (a lambda's body put
                // into a copy, `spec`): the arguments, then that code.
                if let Some((o, inner)) = super::spec::marked(h) {
                    // A definition's function (one no runtime error names,
                    // passed from code of `o`): its arguments that run
                    // bound in order, then the call compiled as code of
                    // `o`, so it is `o`'s copy (`spec::report`) and its
                    // erased arguments are what the call needs (#170).
                    if let Tm::Def(_) = inner {
                        let r = spine.iter().filter(|(_, m)| *m != Mult::Zero).count();
                        let mut j = 0;
                        let call = spine.iter().fold(inner.clone(), |c, (a, m)| {
                            let a = if *m == Mult::Zero {
                                crate::core::rename_free(a, 0, &|v| v + r)
                            } else {
                                j += 1;
                                Tm::Var(r - j)
                            };
                            Tm::App(Rc::new(c), Rc::new(a), Icit::Expl, *m)
                        });
                        let body = Ir::At(o, self.at(o).under(r).compile(&call));
                        // Argument `j` is computed under the `let`s of those before it.
                        let run: Vec<Ir> = spine.iter().filter(|(_, m)| *m != Mult::Zero).enumerate().map(|(j, (a, _))| shift(&self.go(a), j, 0)).collect();
                        return run.into_iter().rev().fold(body, |b, v| Ir::Let(Arc::new(v), Arc::new(b)));
                    }
                    let n = spine.len();
                    let inner = self.at(o).go(&crate::core::rename_free(inner, 0, &|v| v - 1));
                    let call = Ir::Call(Arc::new(shift(&inner, n, 0)), (0..n).rev().map(|i| Arc::new(Ir::Var(i))).collect());
                    return spine.iter().rev().fold(Ir::At(o, Arc::new(call)), |b, (a, m)| {
                        let v = if *m == Mult::Zero { Arc::new(self.erased(a)) } else { self.compile(a) };
                        Ir::Let(v, Arc::new(b))
                    });
                }
                // A lambda applied (an instance's function as its dictionary
                // has it, at a known instance): `let`s, in order, as the
                // call would bind its parameters.
                if let Tm::Lam(x, m, _, b) = h {
                    let mut body = (**b).clone();
                    for (a, am) in &spine[1..] {
                        body = Tm::App(Rc::new(body), Rc::new(crate::core::rename_free(a, 0, &|v| v + 1)), Icit::Expl, *am);
                    }
                    let (a, am) = spine[0];
                    let m = if *m == Mult::Zero || am == Mult::Zero { Mult::Zero } else { *m };
                    // One that computes nothing is put in: a dictionary
                    // stays known. A known function is bound by the `let`
                    // (below), so that it stays known too.
                    if m == Mult::Zero || inert(self.g, a) || known_dict(self.g, a) {
                        return self.go(&subst(&body, &[(**a).clone()], 0));
                    }
                    return self.go(&Tm::Let(x.clone(), m, Rc::new(Tm::Error), a.clone(), Rc::new(body)));
                }
                // A call passing a known instance's dictionary: its copy
                // with the dictionary put in (`spec`).
                let copy = match (h, self.spec) {
                    (Tm::Def(f), Some(cx)) => super::spec::specialize(self.g, cx, self.owner, *f, &spine),
                    _ => None,
                };
                // A function showing values of a type parameter gets that
                // type's descriptor (#170).
                let described = match h {
                    Tm::Def(d) => self.g.well_known.desc_params.get(d),
                    _ => None,
                };
                let put = |k: usize| copy.as_ref().is_some_and(|c| c.put.get(k).copied().unwrap_or(false));
                let gone = |k: usize| copy.as_ref().is_some_and(|c| c.gone.get(k).copied().unwrap_or(false));
                let mut args: Vec<Arc<Ir>> = spine
                    .into_iter()
                    .enumerate()
                    .filter(|(k, _)| !gone(*k))
                    .map(|(k, (a, m))| match m {
                        _ if put(k) => Arc::new(Ir::Erased),
                        Mult::Zero if described.is_some_and(|ps| ps.contains(&k)) => Arc::new(self.descriptor(a)),
                        Mult::Zero => Arc::new(self.erased(a)),
                        _ => self.compile(a),
                    })
                    .collect();
                // A constructor with all its arguments is built directly.
                if let Tm::Con(c) = h {
                    if args.len() == self.g.arity_con(*c) {
                        let ci = &self.g.cons[c.0 as usize];
                        let np = self.g.arity_ty(ci.ty);
                        let (_, targs) = t.spine();
                        if let Some(k) = self.g.unboxed_field(*c) {
                            return if self.g.is_dict_type_field(*c, k) { self.descriptor(targs[np + k]) } else { self.go(targs[np + k]) };
                        }
                        let fields = args
                            .into_iter()
                            .skip(np)
                            .zip(&ci.fields)
                            .enumerate()
                            .map(|(k, (a, f))| match f.1 {
                                Mult::Zero if self.dict_type_field(*c, k) => Arc::new(self.descriptor(targs[np + k])),
                                Mult::Zero => Arc::new(Ir::Erased),
                                _ => a,
                            })
                            .collect();
                        return Ir::Con(*c, fields);
                    }
                }
                match copy {
                    Some(c) => {
                        // The functions' variables, after the arguments the
                        // copy is made for.
                        let tail = args.split_off(c.at - c.gone.iter().filter(|g| **g).count());
                        args.extend(c.caps.iter().map(|v| Arc::new(self.var(*v))));
                        args.extend(tail);
                        Ir::Call(Arc::new(Ir::Global(c.id)), args)
                    }
                    None => Ir::Call(self.compile(h), args),
                }
            }
            Tm::Let(..) if super::spec::marked(t).is_some() => {
                let Some((o, b)) = super::spec::marked(t) else { unreachable!() };
                Ir::At(o, Arc::new(self.at(o).go(&crate::core::rename_free(b, 0, &|v| v - 1))))
            }
            // A variable bound to a known function, as a value.
            Tm::Let(..) if super::spec::known_var(t).is_some() => {
                let Some((v, _)) = super::spec::known_var(t) else { unreachable!() };
                self.go(v)
            }
            // A known function stays known where it is called or passed to
            // a copy (`spec`); its closure is built only if the body uses
            // it otherwise, and then once.
            Tm::Let(_, m, _, v, b) if *m != Mult::Zero => {
                let v = self.know(v);
                if self.known_fn(&v) {
                    let f = super::spec::known_var(&v).map_or(&*v, |(_, f)| f);
                    let bound = Rc::new(super::spec::Bound { f: f.clone(), used: Default::default() });
                    let body = self.knowing(&bound).compile(b);
                    let v = if bound.used.get() { self.compile(&v) } else { Arc::new(Ir::Erased) };
                    return Ir::Let(v, body);
                }
                Ir::Let(self.compile(&v), self.under(1).compile(b))
            }
            Tm::Let(_, _, _, _, b) => Ir::Let(Arc::new(Ir::Erased), self.under(1).compile(b)),
            Tm::Lit(l) => Ir::Lit(lit_value(l)),
            Tm::Known(k) => self.known(k),
            Tm::Tuple(xs) => Ir::Tuple(xs.iter().map(|x| self.compile(x)).collect()),
            Tm::Proj(x, i, rest) => Ir::Proj(self.compile(x), *i, *rest),
            Tm::Field(x, c, i) => match self.g.unboxed_field(*c) {
                Some(k) if k == *i => self.go(x),
                Some(_) => Ir::Erased,
                None => Ir::Field(self.compile(x), *i),
            },
            Tm::ConApp(c, args) => {
                let ci = &self.g.cons[c.0 as usize];
                let np = self.g.arity_ty(ci.ty);
                if let Some(k) = self.g.unboxed_field(*c) {
                    return if self.g.is_dict_type_field(*c, k) { self.descriptor(&args[np + k]) } else { self.go(&args[np + k]) };
                }
                let fields = args[np..]
                    .iter()
                    .zip(&ci.fields)
                    .enumerate()
                    .map(|(k, (a, f))| match f.1 {
                        Mult::Zero if self.dict_type_field(*c, k) => Arc::new(self.descriptor(a)),
                        Mult::Zero => Arc::new(Ir::Erased),
                        _ => self.compile(a),
                    })
                    .collect();
                Ir::Con(*c, fields)
            }
            Tm::PrimApp(p, args) => {
                if let (Prim::Par, [Tm::Tuple(xs)]) = (p, &args[..]) {
                    return Ir::Par(xs.iter().map(|x| self.compile(x)).collect());
                }
                // A call with effects is the call (§7.1).
                if let (Prim::Effect(_), [x]) = (p, &args[..]) {
                    return self.go(x);
                }
                // The flag: `Nat` subtraction (checked), or indexing an
                // `Array U8`, always a bytes object (#624).
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
            Tm::Case(s, c) => match c.branches.first() {
                // A value stored as its one kept field (#170): the arm's
                // fields are that value and erased ones.
                Some((con, n, body)) if self.g.unboxed_field(*con).is_some() => {
                    let k = self.g.unboxed_field(*con).unwrap_or(0);
                    // `s` is bound first, then each field: field `j` sees
                    // `s` at index `j`. The body's other variables move past `s`.
                    let mut ir = shift(&self.under(*n).go(body), 1, *n);
                    for j in (0..*n).rev() {
                        let v = if j == k { Ir::Var(j) } else { Ir::Erased };
                        ir = Ir::Let(Arc::new(v), Arc::new(ir));
                    }
                    Ir::Let(self.compile(s), Arc::new(ir))
                }
                _ => Ir::Case(self.compile(s), Arc::new(self.case(c))),
            },
            Tm::Error => Ir::Fail("no arm of a `match` matches this value"),
        }
    }

    /// The function to call for definition `d` here: its copy whose
    /// runtime errors name this code's owner, if no runtime error names `d`
    /// (`spec::report`).
    fn reported(&self, d: DefId) -> DefId {
        match self.spec {
            Some(cx) => super::spec::report(self.g, cx, self.owner, d),
            None => d,
        }
    }

    /// This compiler, for code of definition `o` (a runtime error in it
    /// names `o`).
    fn at(&self, o: Option<DefId>) -> Compiler<'g> {
        Compiler { owner: o, fns: self.fns.clone(), ..*self }
    }

    /// A known function small enough to substitute (`spec`), where
    /// functions are specialized.
    fn known_fn(&self, t: &Tm) -> bool {
        self.spec.is_some_and(|cx| super::spec::substitutes_fns() && super::spec::small_fn(self.g, cx.staged, t))
    }

    fn case(&self, c: &CaseTm) -> IrCase {
        IrCase {
            branches: c.branches.iter().map(|(con, n, b)| (*con, *n, self.under(*n).compile(b))).collect(),
            lits: c.lits.iter().map(|(l, b)| (lit_value(l), self.compile(b))).collect(),
            default: c.default.as_ref().map(|d| self.compile(d)),
        }
    }

    /// A class's type in its dictionary (#133): a field the dictionary
    /// keeps the type's layout word in, for generic code's arrays of it.
    /// A known value as code: a literal, or static data laid out as the
    /// value is at run time, erased as `Tm::ConApp` is above (a type
    /// stored as its one kept field is that field; an erased field is
    /// nothing, but a dictionary's type descriptor, which the value holds
    /// as it was at run time). A loop over the value's nodes.
    fn known(&self, k: &crate::known::Value) -> Ir {
        use super::lower::{SNode, Static};
        use crate::known::Node;
        use checkers_rt::word as w;
        if let Some(l) = k.lit() {
            return Ir::Lit(lit_value(&l));
        }
        let mut out = Static::default();
        let mut at: crate::known::FxMap<u32, u32> = Default::default();
        for x in k.graph.reachable(k.id) {
            let id = match k.graph.node(x) {
                Node::Int(n) if w::fits(*n) => out.add(SNode::Word(w::mk_int(*n as i64))),
                Node::Int(n) => out.add(SNode::Big(num_bigint::BigInt::from(*n))),
                Node::Big(n) => out.add(SNode::Big(n.clone())),
                Node::Str(s) => out.add(SNode::Bytes(Arc::from(s.as_bytes()))),
                Node::Bytes(b) => out.add(SNode::Bytes(Arc::from(&**b))),
                Node::Unit => out.add(SNode::Word(w::UNIT)),
                Node::Erased => out.add(SNode::Word(w::ERASED)),
                Node::Closure(crate::known::Code::Def(d)) => out.add(SNode::Global(d.0)),
                Node::Closure(crate::known::Code::Con(c)) => out.add(SNode::ConFn(c.0)),
                Node::Closure(crate::known::Code::Lam(code)) => out.add(SNode::Lam(code.clone())),
                Node::Pap(xs) => out.add(SNode::Obj { kind: w::K_PAP, tag: 0, fields: xs.iter().map(|p| at[p]).collect() }),
                Node::Tuple(xs) if xs.is_empty() => out.add(SNode::Word(w::UNIT)),
                Node::Tuple(xs) => out.tuple(xs.iter().map(|p| at[p]).collect()),
                Node::Array(l, xs) => out.add(SNode::Array { layout: *l, elems: xs.iter().map(|p| at[p]).collect() }),
                Node::Con(c, xs) => {
                    let ci = &self.g.cons[c.0 as usize];
                    match self.g.unboxed_field(*c) {
                        Some(f) => at[&xs[f]],
                        None if ci.fields.is_empty() => out.add(SNode::Word(w::nullary(c.0))),
                        None => {
                            let fields = xs
                                .iter()
                                .zip(&ci.fields)
                                .enumerate()
                                .map(|(f, (p, fi))| match fi.1 {
                                    Mult::Zero if !self.dict_type_field(*c, f) => out.add(SNode::Word(w::ERASED)),
                                    _ => at[p],
                                })
                                .collect();
                            out.add(SNode::Obj { kind: w::K_CON, tag: c.0 as u64, fields })
                        }
                    }
                }
            };
            at.insert(x, id);
        }
        Ir::Static(Arc::new(out), at[&k.id])
    }

    fn dict_type_field(&self, c: crate::core::ConId, k: usize) -> bool {
        self.g.is_dict_type_field(c, k)
    }

    /// An erased argument. A type is passed as its layout word (#624): an
    /// array of it is laid out by that word; anything else as nothing.
    fn erased(&self, a: &Tm) -> Ir {
        let h = a.head();
        let typelike = match h {
            Tm::Var(_) | Tm::Meta(_) | Tm::TyCon(_) | Tm::TyConApp(..) => true,
            Tm::Def(d) => self.g.defs.get(d.0 as usize).is_some_and(|i| matches!(i.ty, Tm::Univ(_))) || self.g.assoc_field(*d).is_some(),
            _ => false,
        };
        if !typelike {
            return Ir::Erased;
        }
        let depth = max_var(a).map_or(0, |m| m + 1);
        let env = (0..depth).map(Val::var).collect::<crate::core::Env>();
        let v = eval(self.g, &env, a);
        // A class's type at a dictionary passed at run time (#133): its
        // layout word, kept in the dictionary.
        if let Val::Neutral(Head::Var(x), sp) = crate::core::force(self.g, v.clone()) {
            if let [Elim::Field(c, i)] = sp.as_slice() {
                if x < depth && self.dict_type_field(*c, *i) {
                    return self.dict_field(depth - 1 - x, *c, *i);
                }
            }
        }
        match crate::core::layout_of(self.g, &v) {
            Ok(0) => Ir::Erased,
            Ok(l) => Ir::Lit(Lit::Num(l as i128)),
            Err(level) if level < depth => self.var(depth - 1 - level),
            Err(_) => Ir::Erased,
        }
    }

    /// A function computing the descriptor of field `k` of constructor `c`,
    /// whose type `t` is computed from earlier fields (#170): it takes the
    /// type's parameters' descriptors, then those fields' values.
    pub fn field_type_fn(&self, c: crate::core::ConId, k: usize, t: &Tm) -> Ir {
        let n = self.g.arity_ty(self.g.cons[c.0 as usize].ty) + k;
        (0..n).fold(self.under(n).type_code(t), |b, _| Ir::Lam(self.owner, Arc::new(b)))
    }

    /// Code computing a type's descriptor: `match`es on values (earlier
    /// fields) pick the type; each type picked is described.
    fn type_code(&self, t: &Tm) -> Ir {
        match t {
            Tm::Case(s, c) => match c.branches.first() {
                Some((con, n, body)) if self.g.unboxed_field(*con).is_some() => {
                    let k = self.g.unboxed_field(*con).unwrap_or(0);
                    let mut ir = shift(&self.under(*n).type_code(body), 1, *n);
                    for j in (0..*n).rev() {
                        let v = if j == k { Ir::Var(j) } else { Ir::Erased };
                        ir = Ir::Let(Arc::new(v), Arc::new(ir));
                    }
                    Ir::Let(self.compile(s), Arc::new(ir))
                }
                _ => Ir::Case(
                    self.compile(s),
                    Arc::new(IrCase {
                        branches: c.branches.iter().map(|(con, n, b)| (*con, *n, Arc::new(self.under(*n).type_code(b)))).collect(),
                        lits: c.lits.iter().map(|(l, b)| (lit_value(l), Arc::new(self.type_code(b)))).collect(),
                        default: c.default.as_ref().map(|d| Arc::new(self.type_code(d))),
                    }),
                ),
            },
            Tm::Let(_, m, _, v, b) => {
                let v = if *m == Mult::Zero { Arc::new(Ir::Erased) } else { self.compile(v) };
                Ir::Let(v, Arc::new(self.under(1).type_code(b)))
            }
            _ => self.descriptor(t),
        }
    }

    /// A type argument's descriptor (#170): built from its arguments'
    /// descriptors, a type variable's word, or a dictionary's type.
    fn descriptor(&self, a: &Tm) -> Ir {
        let depth = max_var(a).map_or(0, |m| m + 1);
        let env = (0..depth).map(Val::var).collect::<crate::core::Env>();
        let v = eval(self.g, &env, a);
        self.desc_ir(&crate::core::desc_of(self.g, &v), depth)
    }

    /// Field `i` of the dictionary at index `x`, of constructor `c`: the
    /// dictionary itself if that is its only kept field (#170).
    fn dict_field(&self, x: usize, c: crate::core::ConId, i: usize) -> Ir {
        if self.g.unboxed_field(c) == Some(i) {
            self.var(x)
        } else {
            Ir::Field(Arc::new(self.var(x)), i)
        }
    }

    fn desc_ir(&self, d: &crate::core::Desc, depth: usize) -> Ir {
        use crate::core::Desc;
        match d {
            Desc::Known(tag, args) if args.is_empty() => Ir::Lit(Lit::Num(*tag as i128)),
            Desc::Known(tag, args) => {
                let mut parts: Vec<Arc<Ir>> = args.iter().map(|x| Arc::new(self.desc_ir(x, depth))).collect();
                parts.push(Arc::new(Ir::Lit(Lit::Num(*tag as i128))));
                Ir::Tuple(parts)
            }
            Desc::Var(level) if *level < depth => self.var(depth - 1 - level),
            Desc::Dict(level, c, i) if *level < depth => self.dict_field(depth - 1 - level, *c, *i),
            // A value: computed here, and marked as one.
            Desc::Value(v) => {
                let t = crate::core::quote(self.g, depth, v);
                let tag = checkers_rt::desc::tag(Some(checkers_rt::desc::VALUE), 0);
                Ir::Tuple(vec![Arc::new(self.go(&t)), Arc::new(Ir::Lit(Lit::Num(tag as i128)))])
            }
            Desc::Apply(level, args) if *level < depth => args.iter().fold(self.var(depth - 1 - level), |f, a| {
                Ir::Prim(Op::TypeApply, vec![Arc::new(f), Arc::new(self.desc_ir(a, depth))], false)
            }),
            _ => Ir::Erased,
        }
    }

    /// Is this element type `U8`, so the array is a bytes object (#624)?
    fn is_bytes_elem(&self, ty: &Tm) -> bool {
        let depth = max_var(ty).map_or(0, |m| m + 1);
        let env = (0..depth).map(Val::var).collect::<crate::core::Env>();
        crate::core::layout_of(self.g, &eval(self.g, &env, ty)) == Ok(checkers_rt::array::Layout::U8 as u8)
    }

    /// Is this type term `Nat`? It may mention local variables and solved metas.
    fn is_nat(&self, ty: &Tm) -> bool {
        let depth = max_var(ty).map_or(0, |m| m + 1);
        let env = (0..depth).map(Val::var).collect::<crate::core::Env>();
        crate::core::is_nat(self.g, &eval(self.g, &env, ty))
    }
}

/// `t`, under `depth` binders of the body of a closed function of
/// `args.len()` parameters, with those parameters replaced by `args`.
fn subst(t: &Tm, args: &[Tm], depth: usize) -> Tm {
    match t {
        Tm::Var(i) if *i >= depth && i - depth < args.len() => {
            crate::core::rename_free(&args[args.len() - 1 - (i - depth)], 0, &|x| x + depth)
        }
        Tm::Var(i) if *i >= depth => Tm::Var(i - args.len()),
        _ => t.map_sub(|x, n| subst(x, args, depth + n)),
    }
}


/// Shift the free de Bruijn indices of `ir` from `cutoff` on up by `k`.
pub fn shift(ir: &Ir, k: usize, cutoff: usize) -> Ir {
    fn go(ir: &Ir, k: usize, depth: usize) -> Ir {
        let a = |x: &Arc<Ir>, d: usize| Arc::new(go(x, k, d));
        let all = |xs: &[Arc<Ir>], d: usize| xs.iter().map(|x| a(x, d)).collect::<Vec<_>>();
        match ir {
            Ir::Var(i) if *i >= depth => Ir::Var(i + k),
            Ir::Var(i) => Ir::Var(*i),
            Ir::Global(d) => Ir::Global(*d),
            Ir::Erased => Ir::Erased,
            Ir::Lit(v) => Ir::Lit(v.clone()),
            Ir::Lam(o, b) => Ir::Lam(*o, a(b, depth + 1)),
            Ir::Call(h, xs) => Ir::Call(a(h, depth), all(xs, depth)),
            Ir::Let(v, b) => Ir::Let(a(v, depth), a(b, depth + 1)),
            Ir::Tuple(xs) => Ir::Tuple(all(xs, depth)),
            Ir::Proj(x, i, r) => Ir::Proj(a(x, depth), *i, *r),
            Ir::Field(x, i) => Ir::Field(a(x, depth), *i),
            Ir::Con(c, xs) => Ir::Con(*c, all(xs, depth)),
            Ir::ConFn(c) => Ir::ConFn(*c),
            Ir::Prim(op, xs, n) => Ir::Prim(*op, all(xs, depth), *n),
            Ir::Par(xs) => Ir::Par(all(xs, depth)),
            Ir::Case(s, c) => Ir::Case(
                a(s, depth),
                Arc::new(IrCase {
                    branches: c.branches.iter().map(|(con, n, b)| (*con, *n, a(b, depth + n))).collect(),
                    lits: c.lits.iter().map(|(l, b)| (l.clone(), a(b, depth))).collect(),
                    default: c.default.as_ref().map(|d| a(d, depth)),
                }),
            ),
            Ir::At(o, x) => Ir::At(*o, a(x, depth)),
            Ir::Fail(m) => Ir::Fail(m),
            Ir::Static(v, id) => Ir::Static(v.clone(), *id),
        }
    }
    go(ir, k, cutoff)
}

/// A class's function at a known instance's dictionary, as a direct
/// call of that instance's function (§14; and for its preconditions,
/// #225): `f {Seq (Array a)} xs` is
/// `Seq (Array a).f a xs`, the field the dictionary's function would
/// build, with the dictionary's arguments (its types and its context's
/// dictionaries). Building a dictionary does nothing but allocate, so
/// not building it changes no result; the call's own arguments are
/// passed in the same order. `None` when `t` isn't such a call.
pub fn known_instance(g: &Globals, t: &Tm) -> Option<Tm> {
    let wk = &g.well_known;
    let mut spine = Vec::new();
    let mut h = t;
    while let Tm::App(f, a, i, m) = h {
        spine.push((a.clone(), *i, *m));
        h = f;
    }
    spine.reverse();
    let Tm::Def(f) = h else { return None };
    if !wk.class_fns.contains(f) {
        return None;
    }
    // The class's function: `\ … {d} x y -> d.f x y`.
    let mut body = g.defs.get(f.0 as usize)?.body.as_ref()?;
    let mut mults = Vec::new();
    while let Tm::Lam(_, m, _, b) = body {
        mults.push(*m);
        body = b;
    }
    let k = mults.len();
    if spine.len() < k {
        return None;
    }
    let mut read = Vec::new();
    let mut r = body;
    while let Tm::App(g, a, i, m) = r {
        read.push((a.clone(), *i, *m));
        r = g;
    }
    read.reverse();
    let Tm::Field(x, con, field) = r else { return None };
    let Tm::Var(j) = **x else { return None };
    if j >= k {
        return None;
    }
    // Each parameter it keeps is passed once, in order: the call
    // evaluates the same arguments in the same order. An argument that
    // computes nothing (a variable, a literal, a dictionary built from
    // instances, as a class's function's own clauses pass theirs) may
    // be passed in another place.
    let mut passed = Vec::new();
    for (a, _, _) in &read {
        match **a {
            Tm::Var(v) if v < k && v != j && !passed.contains(&(k - 1 - v)) => passed.push(k - 1 - v),
            _ => return None,
        }
    }
    let kept: Vec<usize> = (0..k).filter(|p| mults[*p] != Mult::Zero && *p != k - 1 - j).collect();
    let passed_kept: Vec<usize> = passed.iter().copied().filter(|p| mults[*p] != Mult::Zero).collect();
    let mut sorted = passed_kept.clone();
    sorted.sort_unstable();
    let inert = |p: &usize| inert(g, &spine[*p].0) || known_dict(g, &spine[*p].0);
    let computed: Vec<usize> = passed_kept.iter().copied().filter(|p| !inert(p)).collect();
    if sorted != kept || computed.windows(2).any(|w| w[0] >= w[1]) {
        return None;
    }
    // The dictionary: an instance's function applied to all its arguments.
    let dict = &spine[k - 1 - j].0;
    let (dh, dargs) = dict.spine();
    let Tm::Def(b) = dh else { return None };
    if !wk.dict_fns.contains(b) {
        return None;
    }
    let mut built = g.defs.get(b.0 as usize)?.body.as_ref()?;
    let mut bmults = Vec::new();
    while let Tm::Lam(_, m, _, x) = built {
        bmults.push(*m);
        built = x;
    }
    if bmults.len() != dargs.len() {
        return None;
    }
    // Its kept arguments (the context's dictionaries) are dictionaries
    // in scope or known instances': values, computed by nothing else.
    if !dargs.iter().zip(&bmults).all(|(a, m)| *m == Mult::Zero || known_dict(g, a)) {
        return None;
    }
    let (bh, fields) = built.spine_cloned();
    let (c, all) = match (built, bh) {
        (Tm::ConApp(c, v), _) => (*c, v.clone()),
        (_, Tm::Con(c)) if fields.len() == g.arity_con(*c) => (*c, fields),
        _ => return None,
    };
    if c != *con {
        return None;
    }
    let np = g.arity_ty(g.cons[c.0 as usize].ty);
    let member = all.get(np + field)?;
    let dargs: Vec<Tm> = dargs.iter().map(|a| (***a).clone()).collect();
    let mut out = subst(member, &dargs, 0);
    let mut args = Vec::new();
    for (a, i, m) in &read {
        let Tm::Var(v) = **a else { return None };
        args.push((spine[k - 1 - v].0.clone(), *i, *m));
    }
    args.extend(spine[k..].iter().cloned());
    // A field of a polymorphic function (a class over a type
    // constructor) takes its own types first: they are erased, so
    // substituted.
    let mut args = args.into_iter().peekable();
    while let (Tm::Lam(_, Mult::Zero, _, b), Some(_)) = (&out, args.peek()) {
        let (a, _, _) = args.next()?;
        out = subst(b, &[(*a).clone()], 0);
    }
    Some(args.fold(out, |f, (a, i, m)| Tm::App(Rc::new(f), a, i, m)))
}

/// A term that computes nothing: a variable, a literal, or a constant whose
/// value is known at compile time (which is compiled as that value, §8.9).
pub fn inert(g: &Globals, t: &Tm) -> bool {
    match t {
        Tm::Var(_) | Tm::Lit(_) => true,
        Tm::Def(d) => crate::core::known_const(g, *d).is_some(),
        _ => false,
    }
}

/// A dictionary computed by nothing but building dictionaries: a
/// variable, or an instance's function applied to such dictionaries
/// and types.
pub fn known_dict(g: &Globals, t: &Tm) -> bool {
    match t.spine() {
        (Tm::Var(_), args) => args.is_empty(),
        (Tm::Def(b), args) if g.well_known.dict_fns.contains(b) => {
            let mut built = g.defs.get(b.0 as usize).and_then(|i| i.body.as_ref());
            args.iter().all(|a| match built {
                Some(Tm::Lam(_, m, _, x)) => {
                    built = Some(x);
                    *m == Mult::Zero || known_dict(g, a)
                }
                _ => false,
            })
        }
        _ => false,
    }
}


impl Ir {
    /// The immediate subterms, each with the number of variables it is under
    /// that `self` binds.
    pub fn subterms(&self) -> Vec<(&Ir, usize)> {
        match self {
            Ir::Var(_) | Ir::Global(_) | Ir::Erased | Ir::Lit(_) | Ir::ConFn(_) | Ir::Fail(_) | Ir::Static(..) => Vec::new(),
            Ir::Lam(_, b) => vec![(&**b, 1)],
            Ir::Call(h, xs) => std::iter::once(&**h).chain(xs.iter().map(|x| &**x)).map(|x| (x, 0)).collect(),
            Ir::Let(v, b) => vec![(&**v, 0), (&**b, 1)],
            Ir::Tuple(xs) | Ir::Con(_, xs) | Ir::Prim(_, xs, _) | Ir::Par(xs) => xs.iter().map(|x| (&**x, 0)).collect(),
            Ir::Proj(x, _, _) | Ir::Field(x, _) | Ir::At(_, x) => vec![(&**x, 0)],
            Ir::Case(s, c) => {
                let mut out = vec![(&**s, 0)];
                out.extend(c.branches.iter().map(|(_, n, b)| (&**b, *n)));
                out.extend(c.lits.iter().map(|(_, b)| (&**b, 0)));
                out.extend(c.default.iter().map(|d| (&**d, 0)));
                out
            }
        }
    }

    /// The same node with each immediate subterm `s` replaced by `f(s, k)`,
    /// `k` being the number of variables `self` binds around it.
    pub fn map_subterms(&self, mut f: impl FnMut(&Ir, usize) -> Ir) -> Ir {
        let mut a = |x: &Arc<Ir>, k: usize| Arc::new(f(x, k));
        match self {
            Ir::Var(i) => Ir::Var(*i),
            Ir::Global(d) => Ir::Global(*d),
            Ir::Erased => Ir::Erased,
            Ir::Lit(v) => Ir::Lit(v.clone()),
            Ir::ConFn(c) => Ir::ConFn(*c),
            Ir::Fail(m) => Ir::Fail(m),
            Ir::Static(v, id) => Ir::Static(v.clone(), *id),
            Ir::Lam(o, b) => Ir::Lam(*o, a(b, 1)),
            Ir::Call(h, xs) => {
                let h = a(h, 0);
                Ir::Call(h, xs.iter().map(|x| a(x, 0)).collect())
            }
            Ir::Let(v, b) => {
                let v = a(v, 0);
                Ir::Let(v, a(b, 1))
            }
            Ir::Tuple(xs) => Ir::Tuple(xs.iter().map(|x| a(x, 0)).collect()),
            Ir::Con(c, xs) => Ir::Con(*c, xs.iter().map(|x| a(x, 0)).collect()),
            Ir::Prim(op, xs, n) => Ir::Prim(*op, xs.iter().map(|x| a(x, 0)).collect(), *n),
            Ir::Par(xs) => Ir::Par(xs.iter().map(|x| a(x, 0)).collect()),
            Ir::Proj(x, i, r) => Ir::Proj(a(x, 0), *i, *r),
            Ir::Field(x, i) => Ir::Field(a(x, 0), *i),
            Ir::At(o, x) => Ir::At(*o, a(x, 0)),
            Ir::Case(s, c) => {
                let s = a(s, 0);
                let branches = c.branches.iter().map(|(con, n, b)| (*con, *n, a(b, *n))).collect();
                let lits = c.lits.iter().map(|(l, b)| (l.clone(), a(b, 0))).collect();
                let default = c.default.as_ref().map(|d| a(d, 0));
                Ir::Case(s, Arc::new(IrCase { branches, lits, default }))
            }
        }
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
        Ir::Proj(x, _, _) | Ir::Field(x, _) | Ir::At(_, x) => globals_in(x, out),
        // The functions static data holds.
        Ir::Static(v, id) => {
            for x in v.reachable(*id) {
                match v.node(x) {
                    super::lower::SNode::Global(d) => out.push(DefId(*d)),
                    super::lower::SNode::Lam(code) => globals_in(&code.ir, out),
                    _ => {}
                }
            }
        }
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

/// What `write_text` asks its caller to name: a definition, a
/// constructor, static data, or whose code a part is.
pub enum Named<'a> {
    Def(DefId),
    Con(ConId),
    Static(&'a Arc<super::lower::Static>, u32),
    Owner(Option<DefId>),
}

/// Code written exactly, as text: equal texts, equal code. `name` writes
/// what the text names (`None`: it can't, and neither can the text).
/// Recursive over the code's nesting, as compiling it is.
pub fn write_text(ir: &Ir, name: &mut dyn FnMut(Named, &mut String) -> Option<()>, out: &mut String) -> Option<()> {
    use std::fmt::Write;
    let list = |xs: &[Arc<Ir>], name: &mut dyn FnMut(Named, &mut String) -> Option<()>, out: &mut String| -> Option<()> {
        out.push('(');
        for x in xs {
            write_text(x, name, out)?;
            out.push(',');
        }
        out.push(')');
        Some(())
    };
    match ir {
        Ir::Var(i) => write!(out, "v{i}").unwrap(),
        Ir::Global(d) => name(Named::Def(*d), out)?,
        Ir::Erased => out.push('_'),
        Ir::Lit(Lit::Num(n)) => write!(out, "{n}").unwrap(),
        Ir::Lit(Lit::Big(s)) => write!(out, "big{s}").unwrap(),
        Ir::Lit(Lit::Str(s)) => write!(out, "{s:?}").unwrap(),
        Ir::Lit(Lit::Bytes(b)) => write!(out, "b{b:?}").unwrap(),
        Ir::Lam(o, b) => {
            out.push('\\');
            name(Named::Owner(*o), out)?;
            out.push('.');
            write_text(b, name, out)?;
        }
        Ir::Call(h, xs) => {
            out.push('@');
            write_text(h, name, out)?;
            list(xs, name, out)?;
        }
        Ir::Let(v, b) => {
            out.push_str("let ");
            write_text(v, name, out)?;
            out.push(';');
            write_text(b, name, out)?;
        }
        Ir::Tuple(xs) => {
            out.push('t');
            list(xs, name, out)?;
        }
        Ir::Proj(x, i, r) => {
            write!(out, "proj{i}{r} ").unwrap();
            write_text(x, name, out)?;
        }
        Ir::Field(x, i) => {
            write!(out, "field{i} ").unwrap();
            write_text(x, name, out)?;
        }
        Ir::Con(c, xs) => {
            out.push('c');
            name(Named::Con(*c), out)?;
            list(xs, name, out)?;
        }
        Ir::ConFn(c) => {
            out.push('f');
            name(Named::Con(*c), out)?;
        }
        Ir::Prim(op, xs, nat) => {
            write!(out, "{op:?}{nat}").unwrap();
            list(xs, name, out)?;
        }
        Ir::Par(xs) => {
            out.push_str("par");
            list(xs, name, out)?;
        }
        Ir::Case(s, c) => {
            out.push_str("case ");
            write_text(s, name, out)?;
            out.push('{');
            for (con, n, b) in &c.branches {
                name(Named::Con(*con), out)?;
                write!(out, " {n}->").unwrap();
                write_text(b, name, out)?;
                out.push(';');
            }
            for (l, b) in &c.lits {
                write_text(&Ir::Lit(l.clone()), name, out)?;
                out.push_str("->");
                write_text(b, name, out)?;
                out.push(';');
            }
            if let Some(d) = &c.default {
                out.push_str("_->");
                write_text(d, name, out)?;
            }
            out.push('}');
        }
        Ir::At(o, x) => {
            out.push_str("at ");
            name(Named::Owner(*o), out)?;
            out.push(' ');
            write_text(x, name, out)?;
        }
        Ir::Fail(m) => write!(out, "fail{m:?}").unwrap(),
        Ir::Static(v, id) => name(Named::Static(v, *id), out)?,
    }
    Some(())
}

/// The free variables of `ir`, as indices outside it.
pub fn free_vars(ir: &Ir, out: &mut std::collections::BTreeSet<usize>) {
    fn go(ir: &Ir, depth: usize, out: &mut std::collections::BTreeSet<usize>) {
        match ir {
            Ir::Var(i) if *i >= depth => {
                out.insert(i - depth);
            }
            _ => {
                for (x, n) in ir.subterms() {
                    go(x, depth + n, out);
                }
            }
        }
    }
    go(ir, 0, out)
}

/// `ir` with each definition `d` it refers to replaced by `f(d)`, where
/// that is some closed code.
pub fn map_globals(ir: &Ir, f: &dyn Fn(DefId) -> Option<Ir>) -> Ir {
    match ir {
        Ir::Global(d) => f(*d).unwrap_or(Ir::Global(*d)),
        _ => ir.map_subterms(|x, _| map_globals(x, f)),
    }
}

/// `ir` with each free variable `i` renamed to `f(i)`.
pub fn rename(ir: &Ir, f: &dyn Fn(usize) -> usize) -> Ir {
    fn go(ir: &Ir, f: &dyn Fn(usize) -> usize, depth: usize) -> Ir {
        match ir {
            Ir::Var(i) if *i >= depth => Ir::Var(f(i - depth) + depth),
            _ => ir.map_subterms(|x, n| go(x, f, depth + n)),
        }
    }
    go(ir, f, 0)
}

/// `ir`, under `m` lambdas, with the variables they bind replaced by
/// closed code `args` (the first lambda's by the first): the body.
pub fn apply_closed(ir: &Ir, args: &[Arc<Ir>]) -> Ir {
    fn go(ir: &Ir, args: &[Arc<Ir>], depth: usize) -> Ir {
        let m = args.len();
        match ir {
            Ir::Var(i) if *i >= depth && i - depth < m => shift(&args[m - 1 - (i - depth)], 0, 0),
            Ir::Var(i) if *i >= depth => Ir::Var(i - m),
            _ => ir.map_subterms(|x, n| go(x, args, depth + n)),
        }
    }
    let mut b = ir;
    for _ in args {
        match b {
            Ir::Lam(_, x) => b = x,
            _ => unreachable!("code under as many lambdas as arguments"),
        }
    }
    go(b, args, 0)
}

/// Code shown as the type checker shows a term (`core::show`), at
/// precedence `p` (0: anywhere, 1: an operand, 2: an argument): a known
/// lambda's code (§8.9), with `names` the text of each variable in scope
/// (the values it captured, then its parameters'). Erased arguments aren't
/// shown; a variable is named as it is bound, the first of `x`, `y`, `z`,
/// `w`, `x1`, … not in scope.
pub fn show_code(g: &Globals, ir: &Ir, names: &mut Vec<String>, p: u8) -> String {
    let paren = |c: bool, s: String| if c { format!("({s})") } else { s };
    let fresh = |names: &Vec<String>| {
        (0..).map(|k| if k < 4 { ["x", "y", "z", "w"][k].to_string() } else { format!("{}{}", ["x", "y", "z", "w"][k % 4], k / 4) }).find(|x| !names.contains(x)).expect("a name")
    };
    let con_name = |c: ConId| g.cons[c.0 as usize].name.to_string();
    match ir {
        Ir::Var(i) => names.get(names.len().wrapping_sub(1 + i)).cloned().unwrap_or_else(|| "_".into()),
        Ir::Global(d) => g.defs.get(d.0 as usize).map_or_else(|| "_".into(), |i| i.name.to_string()),
        Ir::Erased | Ir::Fail(_) => "_".into(),
        Ir::Lit(Lit::Num(n)) => n.to_string(),
        Ir::Lit(Lit::Big(s)) => s.to_string(),
        Ir::Lit(Lit::Str(s)) => format!("{s:?}"),
        Ir::Lit(Lit::Bytes(b)) => format!("b{:?}", String::from_utf8_lossy(b)),
        Ir::Lam(_, b) => {
            let x = fresh(names);
            names.push(x.clone());
            let s = format!("\\{x} -> {}", show_code(g, b, names, 0));
            names.pop();
            paren(p > 0, s)
        }
        Ir::Call(h, args) => {
            let args: Vec<&Arc<Ir>> = args.iter().filter(|a| !matches!(***a, Ir::Erased)).collect();
            if args.is_empty() {
                return show_code(g, h, names, p);
            }
            let mut s = show_code(g, h, names, 2);
            for a in args {
                s += " ";
                s += &show_code(g, a, names, 2);
            }
            paren(p > 1, s)
        }
        Ir::Let(v, b) => {
            let vs = show_code(g, v, names, 0);
            let x = fresh(names);
            names.push(x.clone());
            let s = format!("let {x} = {vs}; {}", show_code(g, b, names, 0));
            names.pop();
            paren(p > 0, s)
        }
        Ir::Tuple(xs) => format!("({})", xs.iter().map(|x| show_code(g, x, names, 0)).collect::<Vec<_>>().join(", ")),
        Ir::Proj(x, i, _) | Ir::Field(x, i) => format!("{}.{i}", show_code(g, x, names, 2)),
        Ir::At(_, x) => show_code(g, x, names, p),
        Ir::ConFn(c) => con_name(*c),
        Ir::Con(c, xs) => {
            let xs: Vec<&Arc<Ir>> = xs.iter().filter(|a| !matches!(***a, Ir::Erased)).collect();
            if Some(*c) == g.well_known.cons && xs.len() == 2 {
                return paren(p > 0, format!("{} :: {}", show_code(g, xs[0], names, 2), show_code(g, xs[1], names, 1)));
            }
            if xs.is_empty() {
                return if Some(*c) == g.well_known.nil { "[]".into() } else { con_name(*c) };
            }
            let args: Vec<String> = xs.iter().map(|x| show_code(g, x, names, 2)).collect();
            paren(p > 1, format!("{} {}", con_name(*c), args.join(" ")))
        }
        Ir::Prim(op, xs, _) => {
            let sym = match op {
                Op::Add => "+",
                Op::Sub => "-",
                Op::Mul => "*",
                Op::Div => "/",
                Op::Rem => "%",
                Op::Eq => "==",
                Op::Ne => "!=",
                Op::Lt => "<",
                Op::Le => "<=",
                Op::Gt => ">",
                Op::Ge => ">=",
                Op::Concat => "++",
                _ => "",
            };
            match (op, xs.as_slice()) {
                (_, [a, b]) if !sym.is_empty() => paren(p > 0, format!("{} {sym} {}", show_code(g, a, names, 2), show_code(g, b, names, 2))),
                (Op::Neg, [a]) => format!("-{}", show_code(g, a, names, 2)),
                (Op::Index, [a, i, ..]) => format!("{}[{}]", show_code(g, a, names, 2), show_code(g, i, names, 0)),
                _ => {
                    let name = if matches!(op, Op::Len) { "len".to_string() } else { format!("{op:?}").to_lowercase() };
                    let args: Vec<String> = xs.iter().map(|x| show_code(g, x, names, 2)).collect();
                    paren(p > 1, format!("{name} {}", args.join(" ")))
                }
            }
        }
        Ir::Par(xs) => paren(p > 1, format!("par ({})", xs.iter().map(|x| show_code(g, x, names, 0)).collect::<Vec<_>>().join(", "))),
        Ir::Case(s, c) => {
            let wk = &g.well_known;
            let arm = |con: Option<ConId>| c.branches.iter().find(|(b, n, _)| Some(*b) == con && *n == 0).map(|(_, _, b)| b);
            if let (Some(t), Some(f), true) = (arm(wk.true_con), arm(wk.false_con), c.branches.len() == 2) {
                let s = format!("if {} then {} else {}", show_code(g, s, names, 0), show_code(g, t, names, 0), show_code(g, f, names, 0));
                return paren(p > 0, s);
            }
            paren(p > 0, format!("match {} …", show_code(g, s, names, 0)))
        }
        Ir::Static(v, id) => show_static(g, v, *id, p),
    }
}

/// Static data shown as `show_code` shows code. Recursive over the value's
/// depth: code holds small values.
fn show_static(g: &Globals, v: &Arc<super::lower::Static>, id: u32, p: u8) -> String {
    use super::lower::SNode;
    use checkers_rt::word as w;
    let paren = |c: bool, s: String| if c { format!("({s})") } else { s };
    match v.node(id) {
        SNode::Word(x) if w::is_int(*x) => w::int_of(*x).to_string(),
        SNode::Word(x) if *x == w::UNIT => "()".into(),
        SNode::Word(x) if *x & 7 == 2 => {
            let c = ConId((*x >> 3) as u32);
            if Some(c) == g.well_known.nil { "[]".into() } else { g.cons[c.0 as usize].name.to_string() }
        }
        SNode::Word(_) => "_".into(),
        SNode::Big(n) => n.to_string(),
        SNode::Bytes(b) => match std::str::from_utf8(b) {
            Ok(s) => format!("{s:?}"),
            Err(_) => format!("b{:?}", String::from_utf8_lossy(b)),
        },
        SNode::Global(d) => g.defs[*d as usize].name.to_string(),
        SNode::ConFn(c) => g.cons[*c as usize].name.to_string(),
        SNode::Lam(code) => show_code(g, &code.ir, &mut Vec::new(), p),
        SNode::Code(_) => "<function>".into(),
        SNode::Array { elems, .. } => format!("[{}]", elems.iter().map(|e| show_static(g, v, *e, 0)).collect::<Vec<_>>().join(", ")),
        SNode::Obj { kind, fields, .. } if *kind == w::K_TUPLE => format!("({})", fields.iter().map(|e| show_static(g, v, *e, 0)).collect::<Vec<_>>().join(", ")),
        SNode::Obj { kind, tag, fields } if *kind == w::K_CON => {
            let c = ConId(*tag as u32);
            if Some(c) == g.well_known.cons && fields.len() == 2 {
                return paren(p > 0, format!("{} :: {}", show_static(g, v, fields[0], 2), show_static(g, v, fields[1], 1)));
            }
            let args: Vec<String> = fields.iter().filter(|f| !matches!(v.node(**f), SNode::Word(x) if *x == w::ERASED)).map(|f| show_static(g, v, *f, 2)).collect();
            paren(p > 1 && !args.is_empty(), format!("{} {}", g.cons[c.0 as usize].name, args.join(" ")).trim_end().to_string())
        }
        SNode::Obj { fields, .. } => {
            let parts: Vec<String> = fields.iter().map(|f| show_static(g, v, *f, 2)).collect();
            paren(p > 1, parts.join(" "))
        }
    }
}
