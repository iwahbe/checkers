//! Closure conversion (D72, §14): erased code (`native::ir::Ir`,
//! curried and de Bruijn-indexed) becomes first-order functions over
//! numbered variables. Every lambda becomes a function taking its closure
//! (the environment) and its arguments; saturated calls of known functions
//! are direct. Arguments of primitives and builtins are atoms, so that the
//! reference-counting pass can treat them as borrowed.

use crate::core::{ConId, DefId, Globals, Mult, Tm};
use crate::native::ir::{Compiler, Ir, Lit as RtLit, Op};
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

pub type V = u32;

#[derive(Clone)]
pub enum E {
    Var(V),
    Int(i64),
    /// A number too big for a word: its decimal digits.
    BigLit(String),
    Str(Arc<str>),
    Bytes(Arc<[u8]>),
    Erased,
    Unit,
    /// The value of a definition: its global closure, or a constant.
    Global(u32),
    /// A constructor used as a function: its global closure.
    ConFn(u32),
    Let(V, Box<E>, Box<E>),
    /// A saturated call of a known function.
    Call { f: u32, args: Vec<E>, tail: bool },
    /// Apply a function value.
    Apply { f: Box<E>, args: Vec<E>, tail: bool },
    MkClo { f: u32, captured: Vec<V> },
    /// `reuse`: memory of a value being dropped, to build in place (D74).
    Con { con: u32, fields: Vec<E>, reuse: Option<V> },
    Tuple(Vec<E>),
    /// An operation that borrows its (atomic) arguments; `drops` are
    /// dropped after it (filled in by the reference-counting pass).
    Borrow { op: BOp, args: Vec<E>, drops: Vec<V> },
    Case { scrut: V, arms: Vec<Arm>, lits: Vec<(E, E)>, default: Option<Box<E>> },
    /// `par`: closures taking `()`.
    Par(Vec<E>),
    Fail(&'static str),
    // Inserted by the reference-counting pass.
    Dup(V, Box<E>),
    Drop(V, Box<E>),
    /// `DropReuse(x, token, n, e)`: drop `x`, a constructor value with `n`
    /// fields; if it was the only reference, its memory becomes `token`
    /// (else `token` is 0).
    DropReuse(V, V, usize, Box<E>),
}

#[derive(Clone, Copy, Debug)]
pub enum BOp {
    Prim(Op, bool),
    /// A builtin: its runtime symbol.
    Builtin(&'static str),
    Field(usize),
    Proj(usize),
}

#[derive(Clone)]
pub struct Arm {
    pub con: u32,
    /// The variables the arm binds for the constructor's fields (`None`:
    /// not used).
    pub fields: Vec<Option<V>>,
    pub body: E,
}

#[derive(Clone)]
pub enum FnKind {
    /// A definition's function: it ignores its environment.
    Global,
    /// A lambda: its closure holds `captured`.
    Lambda { captured: Vec<V> },
    /// A builtin used as a value: calls the runtime with the kept arguments.
    BuiltinWrap { sym: &'static str, keep: Vec<bool> },
    /// A constructor used as a function.
    ConWrap { con: u32, np: usize, erased: Vec<bool> },
    /// Computes a constant's value (once).
    Caf,
}

#[derive(Clone)]
pub struct Func {
    pub name: String,
    /// The definition this code belongs to (for runtime errors).
    pub owner: u32,
    pub kind: FnKind,
    pub params: Vec<V>,
    pub body: E,
    /// Variables are numbered from 0 to `nvars`.
    pub nvars: u32,
}

/// How a definition is called.
#[derive(Clone)]
pub enum DefShape {
    /// A function of this many parameters: `Func` index.
    Fn { func: u32, arity: usize },
    /// A builtin: runtime symbol, kept-parameter mask, wrapper function.
    Builtin { sym: &'static str, keep: Vec<bool>, wrap: u32 },
    /// A constant computed on first use: `Func` index of its code.
    Caf { func: u32 },
    /// Not available at run time.
    Missing(String),
}

pub struct Program {
    /// Functions; those from `rc_done` on still need reference counting.
    pub funcs: Vec<Func>,
    pub rc_done: usize,
    /// Compiled code of each definition lowered so far.
    pub code: HashMap<u32, Arc<Ir>>,
    pub defs: HashMap<u32, DefShape>,
    /// Constructor wrapper functions, by constructor.
    pub con_wraps: HashMap<u32, u32>,
    /// All definition names (including staged ones), for error messages.
    pub names: Vec<String>,
    /// `main`, when the program has one.
    pub main: u32,
}

/// Code with no definition (a `check`, a value staging computes).
pub const NO_OWNER: u32 = u32::MAX;

/// Adds to a `Program`.
pub struct Lowerer<'a, 'g> {
    g: &'g Globals,
    staged: Option<&'a crate::stage::Staged>,
    p: &'a mut Program,
    // Per function being lowered:
    next: u32,
    owner: u32,
}

/// The arity of code: how many lambdas it starts with.
fn lams(ir: &Ir) -> (usize, &Ir) {
    let mut n = 0;
    let mut b = ir;
    while let Ir::Lam(_, x) = b {
        n += 1;
        b = x;
    }
    (n, b)
}

impl Program {
    pub fn new(g: &Globals, staged: Option<&crate::stage::Staged>) -> Program {
        let mut names: Vec<String> = g.defs.iter().map(|d| d.name.to_string()).collect();
        if let Some(s) = staged {
            names.extend(s.extra.iter().map(|e| e.0.clone()));
        }
        Program {
            funcs: Vec::new(),
            rc_done: 0,
            code: HashMap::new(),
            defs: HashMap::new(),
            con_wraps: HashMap::new(),
            names,
            main: NO_OWNER,
        }
    }
}

/// The whole program reachable from `main`.
pub fn lower(g: &Globals, staged: Option<&crate::stage::Staged>, main: DefId) -> Program {
    let mut p = Program::new(g, staged);
    Lowerer::new(g, staged, &mut p).add_defs(&[main.0]);
    p.main = main.0;
    p
}

impl<'a, 'g> Lowerer<'a, 'g> {
    pub fn new(g: &'g Globals, staged: Option<&'a crate::stage::Staged>, p: &'a mut Program) -> Self {
        Lowerer { g, staged, p, next: 0, owner: 0 }
    }

    /// Lower `roots` and every definition they reach that isn't lowered yet.
    pub fn add_defs(&mut self, roots: &[u32]) {
        let g = self.g;
        let staged = self.staged;
        let ndefs = g.defs.len() + staged.map_or(0, |s| s.extra.len());
        // Compile every new reachable definition.
        let mut new: Vec<u32> = Vec::new();
        let mut referenced = BTreeSet::new();
        let mut todo: Vec<u32> = roots.to_vec();
        while let Some(d) = todo.pop() {
            if self.p.code.contains_key(&d) || self.p.defs.contains_key(&d) || d as usize >= ndefs {
                continue;
            }
            let Some(body) = crate::native::ir::body_of(g, staged, DefId(d)) else {
                referenced.insert(d);
                continue;
            };
            let c = Compiler { g, owner: Some(DefId(d)) }.compile(&body);
            let mut gs = Vec::new();
            globals_in(&c, &mut gs);
            todo.extend(gs.iter().map(|x| x.0));
            self.p.code.insert(d, c);
            new.push(d);
        }
        new.sort_unstable();
        // Shapes first, so calls can be direct.
        for d in &new {
            let (n, _) = lams(&self.p.code[d]);
            let func = self.p.funcs.len() as u32;
            self.p.funcs.push(Func {
                name: self.p.names[*d as usize].clone(),
                owner: *d,
                kind: if n > 0 { FnKind::Global } else { FnKind::Caf },
                params: Vec::new(),
                body: E::Erased,
                nvars: 0,
            });
            self.p.defs.insert(*d, if n > 0 { DefShape::Fn { func, arity: n } } else { DefShape::Caf { func } });
        }
        // Builtins (and anything else without a body).
        for d in referenced {
            if self.p.defs.contains_key(&d) {
                continue;
            }
            let info = &g.defs[d as usize];
            let full = format!("{}.{}", info.module, info.name);
            let shape = match checkers_rt::builtins::NAMES.iter().find(|(n, _)| *n == full) {
                Some((_, sym)) => {
                    let mut keep = Vec::new();
                    let mut t = &info.ty;
                    while let Tm::Pi(_, m, _, _, b) = t {
                        keep.push(*m != Mult::Zero);
                        t = b;
                    }
                    let wrap = self.wrapper(&full, d, FnKind::BuiltinWrap { sym, keep: keep.clone() }, keep.len());
                    DefShape::Builtin { sym, keep, wrap }
                }
                None => DefShape::Missing(full),
            };
            self.p.defs.insert(d, shape);
        }
        for d in &new {
            let ir = self.p.code[d].clone();
            let (DefShape::Fn { func, .. } | DefShape::Caf { func }) = self.p.defs[d].clone() else { continue };
            self.owner = *d;
            self.next = 0;
            let (n, body) = lams(&ir);
            let params: Vec<V> = (0..n).map(|_| self.fresh()).collect();
            let mut ctx: Vec<V> = params.clone();
            let body = self.expr(body, &mut ctx, true);
            let f = &mut self.p.funcs[func as usize];
            f.params = params;
            f.body = body;
            f.nvars = self.next;
        }
    }

    /// A closed term as a function of no arguments (a `Caf` computed
    /// afresh each time it runs): its index.
    pub fn add_closed(&mut self, t: &Tm) -> u32 {
        let ir = Compiler { g: self.g, owner: None }.compile(t);
        let mut gs = Vec::new();
        globals_in(&ir, &mut gs);
        let roots: Vec<u32> = gs.iter().map(|x| x.0).collect();
        self.add_defs(&roots);
        let func = self.p.funcs.len() as u32;
        self.p.funcs.push(Func { name: "check".into(), owner: NO_OWNER, kind: FnKind::Caf, params: Vec::new(), body: E::Erased, nvars: 0 });
        self.owner = NO_OWNER;
        self.next = 0;
        let mut ctx = Vec::new();
        let body = self.expr(&ir, &mut ctx, true);
        let f = &mut self.p.funcs[func as usize];
        f.body = body;
        f.nvars = self.next;
        func
    }
}

impl Lowerer<'_, '_> {
    fn fresh(&mut self) -> V {
        self.next += 1;
        self.next - 1
    }

    /// A wrapper function (builtin or constructor) of `arity` parameters.
    fn wrapper(&mut self, name: &str, owner: u32, kind: FnKind, arity: usize) -> u32 {
        let params: Vec<V> = (0..arity as u32).collect();
        self.p.funcs.push(Func { name: name.to_string(), owner, kind, params, body: E::Erased, nvars: arity as u32 });
        (self.p.funcs.len() - 1) as u32
    }

    fn con_wrap(&mut self, c: u32) -> u32 {
        if let Some(f) = self.p.con_wraps.get(&c) {
            return *f;
        }
        let ci = &self.g.cons[c as usize];
        let np = self.g.arity_ty(ci.ty);
        let erased = ci.fields.iter().map(|f| f.1 == Mult::Zero).collect();
        let name = ci.name.to_string();
        let arity = self.g.arity_con(ConId(c));
        let f = self.wrapper(&name, self.owner, FnKind::ConWrap { con: c, np, erased }, arity);
        self.p.con_wraps.insert(c, f);
        f
    }

    /// An atom for a borrowed position: literals stay; anything else is
    /// bound to a variable first (`binds`, outermost first).
    fn atom(&mut self, e: E, binds: &mut Vec<(V, E)>) -> E {
        match e {
            E::Var(_) | E::Int(_) | E::Str(_) | E::Bytes(_) | E::Erased | E::Unit => e,
            other => {
                let v = self.fresh();
                binds.push((v, other));
                E::Var(v)
            }
        }
    }

    fn wrap(binds: Vec<(V, E)>, e: E) -> E {
        binds.into_iter().rev().fold(e, |acc, (v, x)| E::Let(v, Box::new(x), Box::new(acc)))
    }

    fn borrow(&mut self, op: BOp, args: Vec<E>) -> E {
        let mut binds = Vec::new();
        let args = args.into_iter().map(|a| self.atom(a, &mut binds)).collect();
        Self::wrap(binds, E::Borrow { op, args, drops: Vec::new() })
    }

    fn lit(v: &RtLit) -> E {
        match v {
            RtLit::Num(n) if checkers_rt::word::fits(*n) => E::Int(*n as i64),
            RtLit::Num(n) => E::BigLit(n.to_string()),
            RtLit::Str(s) => E::Str(s.clone()),
            RtLit::Bytes(b) => E::Bytes(b.clone()),
        }
    }

    fn expr(&mut self, ir: &Ir, ctx: &mut Vec<V>, tail: bool) -> E {
        match ir {
            Ir::Var(i) => E::Var(ctx[ctx.len() - 1 - i]),
            Ir::Global(d) => E::Global(d.0),
            Ir::Erased => E::Erased,
            Ir::Lit(v) => Self::lit(v),
            Ir::Fail(m) => E::Fail(m),
            Ir::Lam(..) => self.lambda(ir, ctx),
            Ir::ConFn(c) => {
                if self.g.arity_con(*c) == 0 {
                    E::Con { con: c.0, fields: Vec::new(), reuse: None }
                } else {
                    self.con_wrap(c.0);
                    E::ConFn(c.0)
                }
            }
            Ir::Call(h, args) => self.call(h, args, ctx, tail),
            Ir::Let(v, b) => {
                let ve = self.expr(v, ctx, false);
                let x = self.fresh();
                ctx.push(x);
                let be = self.expr(b, ctx, tail);
                ctx.pop();
                E::Let(x, Box::new(ve), Box::new(be))
            }
            Ir::Tuple(xs) => {
                if xs.is_empty() {
                    return E::Unit;
                }
                E::Tuple(xs.iter().map(|x| self.expr(x, ctx, false)).collect())
            }
            Ir::Proj(x, i) => {
                let xe = self.expr(x, ctx, false);
                self.borrow(BOp::Proj(*i), vec![xe])
            }
            Ir::Field(x, i) => {
                let xe = self.expr(x, ctx, false);
                self.borrow(BOp::Field(*i), vec![xe])
            }
            Ir::Con(c, xs) => E::Con { con: c.0, fields: xs.iter().map(|x| self.expr(x, ctx, false)).collect(), reuse: None },
            Ir::Prim(op, args, nat) => {
                let es: Vec<E> = args.iter().map(|a| self.expr(a, ctx, false)).collect();
                match op {
                    Op::Par => {
                        // `par t` with a non-literal tuple: the tuple itself.
                        es.into_iter().next().unwrap_or(E::Unit)
                    }
                    _ => self.borrow(BOp::Prim(*op, *nat), es),
                }
            }
            Ir::Par(xs) => {
                let thunks = xs.iter().map(|x| self.thunk(x, ctx)).collect();
                E::Par(thunks)
            }
            Ir::Case(s, c) => {
                let se = self.expr(s, ctx, false);
                let (scrut, binds) = match se {
                    E::Var(v) => (v, Vec::new()),
                    other => {
                        let v = self.fresh();
                        (v, vec![(v, other)])
                    }
                };
                let mut arms = Vec::new();
                for (con, n, body) in &c.branches {
                    let fields: Vec<V> = (0..*n).map(|_| self.fresh()).collect();
                    ctx.extend(fields.iter().copied());
                    let b = self.expr(body, ctx, tail);
                    ctx.truncate(ctx.len() - n);
                    let fv = free_vars(&b);
                    arms.push(Arm { con: con.0, fields: fields.into_iter().map(|f| fv.contains(&f).then_some(f)).collect(), body: b });
                }
                let lits = c.lits.iter().map(|(l, b)| (Self::lit(l), self.expr(b, ctx, tail))).collect();
                let default = c.default.as_ref().map(|d| Box::new(self.expr(d, ctx, tail)));
                Self::wrap(binds, E::Case { scrut, arms, lits, default })
            }
        }
    }

    /// A lambda chain at an expression: a new function, and its closure.
    fn lambda(&mut self, ir: &Ir, ctx: &[V]) -> E {
        let (n, body) = lams(ir);
        // Lower the body in a fresh numbering, mapping the enclosing
        // variables it uses to captured ones.
        let saved_next = self.next;
        let outer: Vec<V> = ctx.to_vec();
        self.next = 0;
        // Placeholders for the outer variables, then the parameters.
        let inner_outer: Vec<V> = (0..outer.len()).map(|_| self.fresh()).collect();
        let params: Vec<V> = (0..n).map(|_| self.fresh()).collect();
        let mut inner_ctx: Vec<V> = inner_outer.clone();
        inner_ctx.extend(params.iter().copied());
        let b = self.expr(body, &mut inner_ctx, true);
        let nvars = self.next;
        self.next = saved_next;
        let fv = free_vars(&b);
        // Captured: outer variables the body uses.
        let mut captured_inner = Vec::new();
        let mut captured_outer = Vec::new();
        for (k, iv) in inner_outer.iter().enumerate() {
            if fv.contains(iv) && !captured_inner.contains(iv) {
                captured_inner.push(*iv);
                captured_outer.push(outer[k]);
            }
        }
        // The same outer variable may appear twice in the context (never in
        // practice): keep the first.
        let f = self.p.funcs.len() as u32;
        let owner = self.owner;
        let name = format!("lambda{f}");
        self.p.funcs.push(Func {
            name,
            owner,
            kind: FnKind::Lambda { captured: captured_inner },
            params,
            body: b,
            nvars,
        });
        E::MkClo { f, captured: captured_outer }
    }

    /// A `par` component: a closure taking `()`.
    fn thunk(&mut self, x: &Ir, ctx: &[V]) -> E {
        let lam = Ir::Lam(Some(DefId(self.owner)), Arc::new(shift(x, 1)));
        self.lambda(&lam, ctx)
    }

    fn call(&mut self, h: &Ir, args: &[Arc<Ir>], ctx: &mut Vec<V>, tail: bool) -> E {
        if let Ir::Global(d) = h {
            match self.p.defs.get(&d.0).cloned() {
                Some(DefShape::Fn { func, arity }) if args.len() >= arity => {
                    let es: Vec<E> = args[..arity].iter().map(|a| self.expr(a, ctx, false)).collect();
                    let rest: Vec<E> = args[arity..].iter().map(|a| self.expr(a, ctx, false)).collect();
                    if rest.is_empty() {
                        return E::Call { f: func, args: es, tail };
                    }
                    let inner = E::Call { f: func, args: es, tail: false };
                    return E::Apply { f: Box::new(inner), args: rest, tail };
                }
                Some(DefShape::Builtin { sym, keep, .. }) if args.len() >= keep.len() => {
                    let kept: Vec<E> = args[..keep.len()]
                        .iter()
                        .zip(&keep)
                        .filter(|(_, k)| **k)
                        .map(|(a, _)| a.clone())
                        .collect::<Vec<_>>()
                        .iter()
                        .map(|a| self.expr(a, ctx, false))
                        .collect();
                    let rest: Vec<E> = args[keep.len()..].iter().map(|a| self.expr(a, ctx, false)).collect();
                    let call = self.borrow(BOp::Builtin(sym), kept);
                    if rest.is_empty() {
                        return call;
                    }
                    return E::Apply { f: Box::new(call), args: rest, tail };
                }
                _ => {}
            }
        }
        let f = self.expr(h, ctx, false);
        let es = args.iter().map(|a| self.expr(a, ctx, false)).collect();
        E::Apply { f: Box::new(f), args: es, tail }
    }
}

/// Shift free de Bruijn indices of `ir` up by `k` (for wrapping in a lambda).
fn shift(ir: &Ir, k: usize) -> Ir {
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
            Ir::Proj(x, i) => Ir::Proj(a(x, depth), *i),
            Ir::Field(x, i) => Ir::Field(a(x, depth), *i),
            Ir::Con(c, xs) => Ir::Con(*c, all(xs, depth)),
            Ir::ConFn(c) => Ir::ConFn(*c),
            Ir::Prim(op, xs, n) => Ir::Prim(*op, all(xs, depth), *n),
            Ir::Par(xs) => Ir::Par(all(xs, depth)),
            Ir::Case(s, c) => Ir::Case(
                a(s, depth),
                Arc::new(crate::native::ir::IrCase {
                    branches: c.branches.iter().map(|(con, n, b)| (*con, *n, a(b, depth + n))).collect(),
                    lits: c.lits.iter().map(|(l, b)| (l.clone(), a(b, depth))).collect(),
                    default: c.default.as_ref().map(|d| a(d, depth)),
                }),
            ),
            Ir::Fail(m) => Ir::Fail(m),
        }
    }
    go(ir, k, 0)
}

/// The definitions code refers to.
pub fn globals_in(ir: &Ir, out: &mut Vec<DefId>) {
    crate::native::ir::globals_in(ir, out)
}

/// Free variables of an expression.
pub fn free_vars(e: &E) -> BTreeSet<V> {
    let mut s = BTreeSet::new();
    fv(e, &mut s);
    s
}

fn fv(e: &E, s: &mut BTreeSet<V>) {
    match e {
        E::Var(v) => {
            s.insert(*v);
        }
        E::Let(x, a, b) => {
            fv(a, s);
            let mut inner = BTreeSet::new();
            fv(b, &mut inner);
            inner.remove(x);
            s.extend(inner);
        }
        E::Call { args, .. } | E::Tuple(args) | E::Par(args) => args.iter().for_each(|a| fv(a, s)),
        E::Con { fields, reuse, .. } => {
            fields.iter().for_each(|a| fv(a, s));
            if let Some(r) = reuse {
                s.insert(*r);
            }
        }
        E::Apply { f, args, .. } => {
            fv(f, s);
            args.iter().for_each(|a| fv(a, s));
        }
        E::MkClo { captured, .. } => s.extend(captured.iter().copied()),
        E::Borrow { args, drops, .. } => {
            args.iter().for_each(|a| fv(a, s));
            s.extend(drops.iter().copied());
        }
        E::Case { scrut, arms, lits, default } => {
            s.insert(*scrut);
            for a in arms {
                let mut inner = BTreeSet::new();
                fv(&a.body, &mut inner);
                for f in a.fields.iter().flatten() {
                    inner.remove(f);
                }
                s.extend(inner);
            }
            for (_, b) in lits {
                fv(b, s);
            }
            if let Some(d) = default {
                fv(d, s);
            }
        }
        E::Dup(x, b) | E::Drop(x, b) => {
            s.insert(*x);
            fv(b, s);
        }
        E::DropReuse(x, t, _, b) => {
            s.insert(*x);
            let mut inner = BTreeSet::new();
            fv(b, &mut inner);
            inner.remove(t);
            s.extend(inner);
        }
        _ => {}
    }
}
