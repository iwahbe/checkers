//! Staging (§8.9, D59–D62): evaluate the compile-time stage away.
//!
//! A partial evaluator over core terms. A function with `comptime`
//! parameters is a compile-time function: each call is expanded with those
//! arguments known, `if`/`match` on known values pick their branch, and
//! known computations run at compile time (in the interpreter). What is left
//! is runtime code with no compile-time calls in it. Runtime arguments of an
//! expanded call are `let`-bound first, so they are evaluated exactly once,
//! in order (D41).

use crate::core::{CaseTm, ConId, DefId, Globals, Lit, Mult, Prim, Tm};
use crate::run::value::Value;
use crate::run::{Interp, Io};
use std::rc::Rc;

/// One variable of the term being staged.
#[derive(Clone)]
enum Ent {
    /// Known at compile time: a closed term.
    Stat(Tm),
    /// A runtime variable of the output, by level.
    Dyn(usize),
    /// A type (or other erased term), valid at the given output level.
    Ty(Tm, usize),
}

/// The result of staging a term at output level `lvl`.
enum R {
    /// Known: a closed term.
    S(Tm),
    /// Runtime code, over the output context.
    D(Tm),
}

impl R {
    fn tm(self) -> Tm {
        match self {
            R::S(t) | R::D(t) => t,
        }
    }
}

pub type Res<T> = Result<T, String>;

/// Runtime arguments `let`-bound before an expansion: name, value, multiplicity.
type Lets = Vec<(crate::core::Name, Tm, Mult)>;

/// Does `t` call a compile-time function, so that it needs staging?
pub fn needs_staging(g: &Globals, t: &Tm) -> bool {
    let mut ds = Vec::new();
    defs_in(t, &mut ds);
    ds.iter().any(|d| !g.defs[d.0 as usize].comptime.is_empty())
}

/// Stage a closed term (a function body, with its parameter lambdas).
pub fn stage(g: &Globals, t: &Tm) -> Res<Tm> {
    let io = Io { stdin: Box::new(std::io::empty()), stdout: Box::new(std::io::sink()), stderr: Box::new(std::io::sink()) };
    let mut s = Stager { g, it: Interp::new(g, io), depth: 0 };
    Ok(s.pe(t, &[], 0)?.tm())
}

struct Stager<'g> {
    g: &'g Globals,
    /// Runs compile-time computations.
    it: Interp<'g>,
    /// Nesting of compile-time expansions, against runaway recursion.
    depth: usize,
}

const MAX_DEPTH: usize = 10_000;

impl<'g> Stager<'g> {
    fn pe(&mut self, t: &Tm, env: &[Ent], lvl: usize) -> Res<R> {
        Ok(match t {
            Tm::Var(i) => match &env[env.len() - 1 - i] {
                Ent::Stat(s) => R::S(s.clone()),
                Ent::Dyn(l) => R::D(Tm::Var(lvl - 1 - l)),
                Ent::Ty(s, at) => R::D(shift(s, lvl - at, 0)),
            },
            Tm::Lit(_) | Tm::Def(_) | Tm::Con(_) => R::S(t.clone()),
            Tm::TyCon(_) | Tm::Univ(_) | Tm::Pi(..) | Tm::TupleTy(_) | Tm::TyConApp(..) | Tm::Meta(_) => {
                R::D(resid(t, env, lvl, 0))
            }
            Tm::Lam(x, m, i, b) => {
                let mut env2 = env.to_vec();
                env2.push(Ent::Dyn(lvl));
                let body = self.pe(b, &env2, lvl + 1)?.tm();
                let lam = Tm::Lam(x.clone(), *m, *i, Rc::new(body));
                if closed(&lam, 0) { R::S(lam) } else { R::D(lam) }
            }
            Tm::App(..) => return self.app(t, env, lvl),
            Tm::Let(x, m, ty, v, b) => {
                let mut env2 = env.to_vec();
                if *m == Mult::Zero {
                    env2.push(Ent::Ty(resid(v, env, lvl, 0), lvl));
                    return self.pe(b, &env2, lvl);
                }
                match self.pe(v, env, lvl)? {
                    R::S(s) => {
                        env2.push(Ent::Stat(s));
                        self.pe(b, &env2, lvl)?
                    }
                    R::D(Tm::Var(i)) => {
                        env2.push(Ent::Dyn(lvl - 1 - i));
                        self.pe(b, &env2, lvl)?
                    }
                    R::D(vt) => {
                        env2.push(Ent::Dyn(lvl));
                        let body = self.pe(b, &env2, lvl + 1)?.tm();
                        R::D(Tm::Let(x.clone(), *m, Rc::new(resid(ty, env, lvl, 0)), Rc::new(vt), Rc::new(body)))
                    }
                }
            }
            Tm::Tuple(xs) => {
                let rs = xs.iter().map(|x| self.pe(x, env, lvl)).collect::<Res<Vec<R>>>()?;
                let all = rs.iter().all(|r| matches!(r, R::S(_)));
                let t = Tm::Tuple(rs.into_iter().map(R::tm).collect());
                if all { R::S(t) } else { R::D(t) }
            }
            Tm::ConApp(c, args) => {
                let np = self.g.arity_ty(self.g.cons[c.0 as usize].ty);
                let mut all = true;
                let mut out = Vec::new();
                for (k, a) in args.iter().enumerate() {
                    if k < np {
                        out.push(Tm::Univ(0));
                        continue;
                    }
                    let r = self.pe(a, env, lvl)?;
                    all &= matches!(r, R::S(_));
                    out.push(r.tm());
                }
                let t = Tm::ConApp(*c, out);
                if all { R::S(t) } else { R::D(t) }
            }
            Tm::Proj(x, i) => match self.pe(x, env, lvl)? {
                R::S(s) => match self.whnf(&s) {
                    Some(Tm::Tuple(xs)) => R::S(xs[*i].clone()),
                    _ => R::S(Tm::Proj(Rc::new(s), *i)),
                },
                R::D(d) => R::D(Tm::Proj(Rc::new(d), *i)),
            },
            Tm::Field(x, c, i) => match self.pe(x, env, lvl)? {
                R::S(s) => match self.whnf(&s) {
                    Some(Tm::ConApp(c2, args)) if c2 == *c => {
                        let np = self.g.arity_ty(self.g.cons[c.0 as usize].ty);
                        R::S(args[np + i].clone())
                    }
                    _ => R::S(Tm::Field(Rc::new(s), *c, *i)),
                },
                R::D(d) => R::D(Tm::Field(Rc::new(d), *c, *i)),
            },
            Tm::PrimApp(p, args) => {
                // `Sub` carries its operand type as a third argument.
                let n = if *p == Prim::Sub { 2 } else { args.len() };
                let mut out = Vec::new();
                let mut all = !matches!(p, Prim::When | Prim::Fork | Prim::Join);
                for (k, a) in args.iter().enumerate() {
                    if k >= n {
                        out.push(resid(a, env, lvl, 0));
                        continue;
                    }
                    let r = self.pe(a, env, lvl)?;
                    all &= matches!(r, R::S(_));
                    out.push(r.tm());
                }
                let t = Tm::PrimApp(p.clone(), out);
                if all && closed(&t, 0) {
                    match self.compute(&t) {
                        Some(v) => R::S(v),
                        None => R::D(t),
                    }
                } else {
                    R::D(t)
                }
            }
            Tm::Case(s, c) => return self.case(s, c, env, lvl),
            Tm::Error => R::D(Tm::Error),
        })
    }

    /// Compute a closed term at compile time; `None` if it fails there (it
    /// will fail at run time instead) or its value can't be written as a term.
    fn compute(&mut self, t: &Tm) -> Option<Tm> {
        let v = self.it.eval_closed(t).ok()?;
        reify(self.g, &v)
    }

    /// A known value in constructor or literal form, if it has one.
    fn whnf(&mut self, s: &Tm) -> Option<Tm> {
        match s {
            Tm::Lit(_) | Tm::ConApp(..) | Tm::Tuple(_) => Some(s.clone()),
            _ => self.compute(s),
        }
    }

    fn app(&mut self, t: &Tm, env: &[Ent], lvl: usize) -> Res<R> {
        let mut spine = Vec::new();
        let mut h = t;
        while let Tm::App(f, a, i, m) = h {
            spine.push((a.clone(), *i, *m));
            h = f;
        }
        spine.reverse();
        // Compile-time function: expand.
        if let Tm::Def(d) = h {
            if !self.g.defs[d.0 as usize].comptime.is_empty() {
                return self.expand(*d, &spine, env, lvl);
            }
        }
        let head = self.pe(h, env, lvl)?;
        // A lambda applied (it is output code, over the output context):
        // reduce it, `let`-binding runtime arguments.
        if let R::S(Tm::Lam(..)) | R::D(Tm::Lam(..)) = &head {
            let lam = head.tm();
            return self.beta(&lam, &spine, env, lvl);
        }
        // `(let x = v; f) a` is `let x = v; f a`: v is evaluated first either
        // way, and the function may then reduce.
        if let R::D(Tm::Let(x, m, ty, v, b)) = &head {
            let mut args = Vec::new();
            for (a, i, am) in &spine {
                let at = if *am == Mult::Zero { resid(a, env, lvl, 0) } else { self.pe(a, env, lvl)?.tm() };
                args.push((shift(&at, 1, 0), *i, *am));
            }
            let mut out = (**b).clone();
            for (a, i, am) in args {
                out = Tm::App(Rc::new(out), Rc::new(a), i, am);
            }
            let ident: Vec<Ent> = (0..=lvl).map(Ent::Dyn).collect();
            let inner = self.pe(&out, &ident, lvl + 1)?.tm();
            return Ok(R::D(Tm::Let(x.clone(), *m, ty.clone(), v.clone(), Rc::new(inner))));
        }
        let mut args = Vec::new();
        let mut all = matches!(head, R::S(_));
        for (a, i, m) in &spine {
            if *m == Mult::Zero {
                args.push((resid(a, env, lvl, 0), *i, *m));
                continue;
            }
            let r = self.pe(a, env, lvl)?;
            all &= matches!(r, R::S(_));
            args.push((r.tm(), *i, *m));
        }
        let partial = matches!(h, Tm::Def(d) if { let i = &self.g.defs[d.0 as usize]; i.opaque && i.body.is_some() });
        let mut out = head.tm();
        for (a, i, m) in args {
            out = Tm::App(Rc::new(out), Rc::new(a), i, m);
        }
        // Everything known, and the callee ends (not `partial`): compute it.
        if all && !partial && closed(&out, 0) {
            let erased = erase_types(&out);
            return Ok(match self.compute(&erased) {
                Some(v) => R::S(v),
                None => R::S(out),
            });
        }
        Ok(R::D(out))
    }

    /// Bind the arguments of an expansion: compile-time ones are known;
    /// runtime ones are `let`-bound unless they are variables.
    fn bind_args(
        &mut self,
        spine: &[(Rc<Tm>, crate::core::Icit, Mult)],
        env: &[Ent],
        lvl: usize,
        comptime: &[usize],
        what: &str,
        names: &[crate::core::Name],
    ) -> Res<(Vec<Ent>, Lets, usize)> {
        let mut ents = Vec::new();
        let mut lets = Vec::new();
        let mut l = lvl;
        for (k, (a, _, m)) in spine.iter().enumerate() {
            if *m == Mult::Zero {
                ents.push(Ent::Ty(resid(a, env, lvl, 0), lvl));
                continue;
            }
            // Earlier `let`s shift the argument's output context.
            let r = self.pe(a, env, lvl)?;
            match r {
                R::S(s) => ents.push(Ent::Stat(s)),
                R::D(_) if comptime.contains(&k) => {
                    return Err(format!("an argument of `{what}` that must be known at compile time isn't"));
                }
                R::D(Tm::Var(i)) => ents.push(Ent::Dyn(lvl - 1 - i)),
                R::D(d) => {
                    let x = names.get(k).cloned().unwrap_or_else(|| Rc::from("$a"));
                    lets.push((x, shift(&d, l - lvl, 0), *m));
                    ents.push(Ent::Dyn(l));
                    l += 1;
                }
            }
        }
        Ok((ents, lets, l))
    }

    fn expand(&mut self, d: DefId, spine: &[(Rc<Tm>, crate::core::Icit, Mult)], env: &[Ent], lvl: usize) -> Res<R> {
        let info = &self.g.defs[d.0 as usize];
        let name = info.name.to_string();
        let comptime = info.comptime.clone();
        let ar = arity(&info.ty);
        let mut body = info.body.clone().ok_or_else(|| format!("`{name}` has no body to expand"))?;
        if spine.len() < ar {
            return Err(format!("`{name}` is not called with all its arguments"));
        }
        for _ in 0..ar {
            let Tm::Lam(_, _, _, b) = body else { return Err(format!("`{name}` has an unexpected body")) };
            body = (*b).clone();
        }
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(format!("expanding `{name}` nests too deeply"));
        }
        let mut names = Vec::new();
        let mut ty = &info.ty;
        while let Tm::Pi(x, _, _, _, b) = ty {
            names.push(x.clone());
            ty = b;
        }
        let r = self.apply_body(&body, ar, spine, env, lvl, &comptime, &name, &names);
        self.depth -= 1;
        r
    }

    /// Stage `body` (under `n` parameters) applied to `spine`: the first `n`
    /// arguments are its parameters, any others are applied to its result.
    #[allow(clippy::too_many_arguments)]
    fn apply_body(
        &mut self,
        body: &Tm,
        n: usize,
        spine: &[(Rc<Tm>, crate::core::Icit, Mult)],
        env: &[Ent],
        lvl: usize,
        comptime: &[usize],
        what: &str,
        names: &[crate::core::Name],
    ) -> Res<R> {
        let (ents, lets, l) = self.bind_args(spine, env, lvl, comptime, what, names)?;
        let mut r = self.pe(body, &ents[..n], l)?;
        if spine.len() > n {
            // Apply the rest to the result, then stage that (a lambda reduces).
            let mut out = r.tm();
            for (e, (_, i, m)) in ents[n..].iter().zip(&spine[n..]) {
                let a = match e {
                    Ent::Stat(s) => s.clone(),
                    Ent::Dyn(k) => Tm::Var(l - 1 - k),
                    Ent::Ty(s, at) => shift(s, l - at, 0),
                };
                out = Tm::App(Rc::new(out), Rc::new(a), *i, *m);
            }
            let ident: Vec<Ent> = (0..l).map(Ent::Dyn).collect();
            r = self.pe(&out, &ident, l)?;
        }
        Ok(wrap_lets(r, lets))
    }

    fn beta(&mut self, lam: &Tm, spine: &[(Rc<Tm>, crate::core::Icit, Mult)], env: &[Ent], lvl: usize) -> Res<R> {
        let mut body = lam.clone();
        let mut n = 0;
        let mut names = Vec::new();
        while let (Tm::Lam(x, _, _, b), true) = (&body, n < spine.len()) {
            names.push(x.clone());
            body = (**b).clone();
            n += 1;
        }
        // The lambda's body sees the output context too (its free variables).
        let outer: Vec<Ent> = (0..lvl).map(Ent::Dyn).collect();
        let (ents, lets, l) = self.bind_args(spine, env, lvl, &[], "a function", &names)?;
        let mut benv = outer;
        benv.extend(ents[..n].iter().cloned());
        let mut r = self.pe(&body, &benv, l)?;
        if spine.len() > n {
            let mut out = r.tm();
            for (e, (_, i, m)) in ents[n..].iter().zip(&spine[n..]) {
                let a = match e {
                    Ent::Stat(s) => s.clone(),
                    Ent::Dyn(k) => Tm::Var(l - 1 - k),
                    Ent::Ty(s, at) => shift(s, l - at, 0),
                };
                out = Tm::App(Rc::new(out), Rc::new(a), *i, *m);
            }
            let ident: Vec<Ent> = (0..l).map(Ent::Dyn).collect();
            r = self.pe(&out, &ident, l)?;
        }
        Ok(wrap_lets(r, lets))
    }

    fn case(&mut self, s: &Tm, c: &CaseTm, env: &[Ent], lvl: usize) -> Res<R> {
        let sr = self.pe(s, env, lvl)?;
        if let R::S(st) = &sr {
            if let Some(v) = self.whnf(st) {
                // A known value picks its branch.
                let mut env2 = env.to_vec();
                match &v {
                    Tm::ConApp(con, args) => {
                        let np = self.g.arity_ty(self.g.cons[con.0 as usize].ty);
                        if let Some((_, _, b)) = c.branches.iter().find(|(bc, _, _)| bc == con) {
                            for a in &args[np..] {
                                env2.push(Ent::Stat(a.clone()));
                            }
                            return self.pe(b, &env2, lvl);
                        }
                    }
                    Tm::Lit(l) => {
                        if let Some((_, b)) = c.lits.iter().find(|(x, _)| lit_eq(x, l)) {
                            return self.pe(b, env, lvl);
                        }
                    }
                    _ => {}
                }
                if let Some(d) = &c.default {
                    return self.pe(d, env, lvl);
                }
            }
        }
        // Unknown: a runtime `match`, each branch staged.
        let st = sr.tm();
        let mut branches = Vec::new();
        for (con, n, b) in &c.branches {
            let mut env2 = env.to_vec();
            for k in 0..*n {
                env2.push(Ent::Dyn(lvl + k));
            }
            branches.push((*con, *n, self.pe(b, &env2, lvl + n)?.tm()));
        }
        let mut lits = Vec::new();
        for (l, b) in &c.lits {
            lits.push((l.clone(), self.pe(b, env, lvl)?.tm()));
        }
        let default = match &c.default {
            Some(d) => Some(self.pe(d, env, lvl)?.tm()),
            None => None,
        };
        Ok(R::D(Tm::Case(Rc::new(st), Rc::new(CaseTm { branches, lits, default }))))
    }
}

fn wrap_lets(r: R, lets: Lets) -> R {
    if lets.is_empty() {
        return r;
    }
    let mut out = r.tm();
    for (x, v, m) in lets.into_iter().rev() {
        out = Tm::Let(x, m, Rc::new(Tm::Error), Rc::new(v), Rc::new(out));
    }
    R::D(out)
}

fn lit_eq(a: &Lit, b: &Lit) -> bool {
    match (a, b) {
        (Lit::Num(x), Lit::Num(y)) => x == y,
        (Lit::Str(x), Lit::Str(y)) => x == y,
        (Lit::Bytes(x), Lit::Bytes(y)) => x == y,
        _ => false,
    }
}

fn arity(ty: &Tm) -> usize {
    let mut n = 0;
    let mut t = ty;
    while let Tm::Pi(_, _, _, _, b) = t {
        n += 1;
        t = b;
    }
    n
}

/// A runtime value as a term, where it has one.
fn reify(g: &Globals, v: &Value) -> Option<Tm> {
    Some(match v {
        Value::Num(n) => Tm::Lit(Lit::Num(n.to_string().parse().ok()?)),
        Value::Str(s) => Tm::Lit(Lit::Str(s.clone())),
        Value::Bytes(b) => Tm::Lit(Lit::Bytes(b.clone())),
        Value::Con(c, fields) => con_tm(g, *c, fields)?,
        Value::Tuple(xs) => Tm::Tuple(xs.iter().map(|x| reify(g, x)).collect::<Option<Vec<_>>>()?),
        Value::Erased => Tm::Tuple(vec![]),
        _ => return None,
    })
}

fn con_tm(g: &Globals, c: ConId, fields: &[Value]) -> Option<Tm> {
    let np = g.arity_ty(g.cons[c.0 as usize].ty);
    let mut args: Vec<Tm> = (0..np).map(|_| Tm::Univ(0)).collect();
    for f in fields {
        args.push(reify(g, f)?);
    }
    Some(Tm::ConApp(c, args))
}

/// Replace erased arguments (types) by a placeholder, so a term whose value
/// arguments are all known is closed.
fn erase_types(t: &Tm) -> Tm {
    match t {
        Tm::App(f, a, i, m) => {
            let a = if *m == Mult::Zero { Tm::Univ(0) } else { (**a).clone() };
            Tm::App(Rc::new(erase_types(f)), Rc::new(a), *i, *m)
        }
        _ => t.clone(),
    }
}

/// Substitute the environment into `t` (no evaluation), giving a term at
/// output level `lvl + depth` (`depth` binders inside `t` so far).
fn resid(t: &Tm, env: &[Ent], lvl: usize, depth: usize) -> Tm {
    let go = |x: &Tm, d: usize| resid(x, env, lvl, d);
    match t {
        Tm::Var(i) if *i < depth => t.clone(),
        Tm::Var(i) => match env.get(env.len().wrapping_sub(1 + i - depth)) {
            Some(Ent::Stat(s)) => s.clone(),
            Some(Ent::Dyn(l)) => Tm::Var(lvl + depth - 1 - l),
            Some(Ent::Ty(s, at)) => shift(s, lvl + depth - at, 0),
            None => Tm::Error,
        },
        Tm::Pi(x, m, i, a, b) => Tm::Pi(x.clone(), *m, *i, Rc::new(go(a, depth)), Rc::new(go(b, depth + 1))),
        Tm::Lam(x, m, i, b) => Tm::Lam(x.clone(), *m, *i, Rc::new(go(b, depth + 1))),
        Tm::App(f, a, i, m) => Tm::App(Rc::new(go(f, depth)), Rc::new(go(a, depth)), *i, *m),
        Tm::Let(x, m, ty, v, b) => {
            Tm::Let(x.clone(), *m, Rc::new(go(ty, depth)), Rc::new(go(v, depth)), Rc::new(go(b, depth + 1)))
        }
        Tm::TupleTy(v) => Tm::TupleTy(v.iter().map(|x| go(x, depth)).collect()),
        Tm::Tuple(v) => Tm::Tuple(v.iter().map(|x| go(x, depth)).collect()),
        Tm::TyConApp(c, v) => Tm::TyConApp(*c, v.iter().map(|x| go(x, depth)).collect()),
        Tm::ConApp(c, v) => Tm::ConApp(*c, v.iter().map(|x| go(x, depth)).collect()),
        Tm::PrimApp(p, v) => Tm::PrimApp(p.clone(), v.iter().map(|x| go(x, depth)).collect()),
        Tm::Proj(x, i) => Tm::Proj(Rc::new(go(x, depth)), *i),
        Tm::Field(x, c, i) => Tm::Field(Rc::new(go(x, depth)), *c, *i),
        Tm::Case(s, c) => Tm::Case(
            Rc::new(go(s, depth)),
            Rc::new(CaseTm {
                branches: c.branches.iter().map(|(con, n, b)| (*con, *n, go(b, depth + n))).collect(),
                lits: c.lits.iter().map(|(l, b)| (l.clone(), go(b, depth))).collect(),
                default: c.default.as_ref().map(|b| go(b, depth)),
            }),
        ),
        _ => t.clone(),
    }
}

/// Add `by` to the free variables of `t` (those `>= cut`).
fn shift(t: &Tm, by: usize, cut: usize) -> Tm {
    if by == 0 {
        return t.clone();
    }
    let go = |x: &Tm, c: usize| shift(x, by, c);
    match t {
        Tm::Var(i) if *i >= cut => Tm::Var(i + by),
        Tm::Pi(x, m, i, a, b) => Tm::Pi(x.clone(), *m, *i, Rc::new(go(a, cut)), Rc::new(go(b, cut + 1))),
        Tm::Lam(x, m, i, b) => Tm::Lam(x.clone(), *m, *i, Rc::new(go(b, cut + 1))),
        Tm::App(f, a, i, m) => Tm::App(Rc::new(go(f, cut)), Rc::new(go(a, cut)), *i, *m),
        Tm::Let(x, m, ty, v, b) => {
            Tm::Let(x.clone(), *m, Rc::new(go(ty, cut)), Rc::new(go(v, cut)), Rc::new(go(b, cut + 1)))
        }
        Tm::TupleTy(v) => Tm::TupleTy(v.iter().map(|x| go(x, cut)).collect()),
        Tm::Tuple(v) => Tm::Tuple(v.iter().map(|x| go(x, cut)).collect()),
        Tm::TyConApp(c, v) => Tm::TyConApp(*c, v.iter().map(|x| go(x, cut)).collect()),
        Tm::ConApp(c, v) => Tm::ConApp(*c, v.iter().map(|x| go(x, cut)).collect()),
        Tm::PrimApp(p, v) => Tm::PrimApp(p.clone(), v.iter().map(|x| go(x, cut)).collect()),
        Tm::Proj(x, i) => Tm::Proj(Rc::new(go(x, cut)), *i),
        Tm::Field(x, c, i) => Tm::Field(Rc::new(go(x, cut)), *c, *i),
        Tm::Case(s, c) => Tm::Case(
            Rc::new(go(s, cut)),
            Rc::new(CaseTm {
                branches: c.branches.iter().map(|(con, n, b)| (*con, *n, go(b, cut + n))).collect(),
                lits: c.lits.iter().map(|(l, b)| (l.clone(), go(b, cut))).collect(),
                default: c.default.as_ref().map(|b| go(b, cut)),
            }),
        ),
        _ => t.clone(),
    }
}

/// No variable of `t` reaches outside `depth` binders.
fn closed(t: &Tm, depth: usize) -> bool {
    match t {
        Tm::Var(i) => *i < depth,
        Tm::Pi(_, _, _, a, b) => closed(a, depth) && closed(b, depth + 1),
        Tm::Lam(_, _, _, b) => closed(b, depth + 1),
        Tm::App(a, b, _, _) => closed(a, depth) && closed(b, depth),
        Tm::Let(_, _, a, b, c) => closed(a, depth) && closed(b, depth) && closed(c, depth + 1),
        Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => {
            v.iter().all(|a| closed(a, depth))
        }
        Tm::Proj(a, _) | Tm::Field(a, _, _) => closed(a, depth),
        Tm::Case(s, c) => {
            closed(s, depth)
                && c.branches.iter().all(|(_, n, b)| closed(b, depth + n))
                && c.lits.iter().all(|(_, b)| closed(b, depth))
                && c.default.as_ref().is_none_or(|b| closed(b, depth))
        }
        _ => true,
    }
}

fn defs_in(t: &Tm, out: &mut Vec<DefId>) {
    match t {
        Tm::Def(d) => out.push(*d),
        Tm::Pi(_, _, _, a, b) | Tm::App(a, b, ..) => {
            defs_in(a, out);
            defs_in(b, out);
        }
        Tm::Lam(_, _, _, b) | Tm::Proj(b, _) | Tm::Field(b, _, _) => defs_in(b, out),
        Tm::Let(_, _, a, b, c) => {
            defs_in(a, out);
            defs_in(b, out);
            defs_in(c, out);
        }
        Tm::TyConApp(_, v) | Tm::ConApp(_, v) | Tm::TupleTy(v) | Tm::Tuple(v) | Tm::PrimApp(_, v) => {
            v.iter().for_each(|x| defs_in(x, out))
        }
        Tm::Case(s, c) => {
            defs_in(s, out);
            c.branches.iter().for_each(|(_, _, b)| defs_in(b, out));
            c.lits.iter().for_each(|(_, b)| defs_in(b, out));
            if let Some(b) = &c.default {
                defs_in(b, out);
            }
        }
        _ => {}
    }
}

// ── printing staged code (`checkers stage`) ─────────────────────────────────

/// A staged definition, in Checkers-like layout.
pub fn show_def(g: &Globals, name: &str, body: &Tm) -> String {
    let mut ns: Vec<crate::core::Name> = Vec::new();
    let mut params = Vec::new();
    let mut t = body;
    while let Tm::Lam(x, m, _, b) = t {
        let x = fresh(&ns, x);
        if *m != Mult::Zero {
            params.push(x.to_string());
        }
        ns.push(x);
        t = b;
    }
    let mut out = format!("fn {name}");
    for p in &params {
        out += " ";
        out += p;
    }
    out += " =\n";
    block(g, &mut ns, t, 1, &mut out);
    out
}

fn fresh(ns: &[crate::core::Name], x: &crate::core::Name) -> crate::core::Name {
    let base = x.trim_start_matches('$');
    let base = if base.is_empty() { "x" } else { base };
    let mut cand: crate::core::Name = Rc::from(base);
    let mut k = 1;
    while ns.contains(&cand) && base != "_" {
        cand = Rc::from(format!("{base}{k}"));
        k += 1;
    }
    cand
}

fn block(g: &Globals, ns: &mut Vec<crate::core::Name>, t: &Tm, ind: usize, out: &mut String) {
    let pad = "    ".repeat(ind);
    match t {
        Tm::Let(x, m, _, v, b) => {
            let x = if *m == Mult::Zero { x.clone() } else { fresh(ns, x) };
            if *m != Mult::Zero {
                if x.as_ref() == "_" {
                    out.push_str(&format!("{pad}{}\n", crate::core::show(g, ns, v)));
                } else {
                    out.push_str(&format!("{pad}let {x} = {}\n", crate::core::show(g, ns, v)));
                }
            }
            ns.push(x);
            block(g, ns, b, ind, out);
            ns.pop();
        }
        Tm::Case(s, c) => {
            let wk = &g.well_known;
            let arm = |con: Option<ConId>| c.branches.iter().find(|b| Some(b.0) == con).map(|b| &b.2);
            if let (Some(tb), Some(fb), 2) = (arm(wk.true_con), arm(wk.false_con), c.branches.len()) {
                out.push_str(&format!("{pad}if {}\n", crate::core::show(g, ns, s)));
                block(g, ns, tb, ind + 1, out);
                out.push_str(&format!("{pad}else\n"));
                block(g, ns, fb, ind + 1, out);
                return;
            }
            out.push_str(&format!("{pad}match {}\n", crate::core::show(g, ns, s)));
            for (con, n, b) in &c.branches {
                let ci = &g.cons[con.0 as usize];
                let mut names = Vec::new();
                for k in 0..*n {
                    let f = ci.fields.get(k).map(|f| f.0.clone()).unwrap_or_else(|| Rc::from("x"));
                    let x = fresh(ns, &f);
                    ns.push(x.clone());
                    names.push((x, ci.fields.get(k).map(|f| f.2)));
                }
                let shown: Vec<String> = names
                    .iter()
                    .filter(|(_, i)| *i != Some(crate::core::Icit::Impl))
                    .map(|(x, _)| x.to_string())
                    .collect();
                let pat = if Some(*con) == wk.cons && shown.len() == 2 {
                    format!("{} :: {}", shown[0], shown[1])
                } else if Some(*con) == wk.nil {
                    "[]".to_string()
                } else if shown.is_empty() {
                    ci.name.to_string()
                } else {
                    format!("{} {}", ci.name, shown.join(" "))
                };
                out.push_str(&format!("{pad}    {pat} ->\n"));
                block(g, ns, b, ind + 2, out);
                ns.truncate(ns.len() - n);
            }
            for (l, b) in &c.lits {
                let lt = crate::core::show(g, ns, &Tm::Lit(l.clone()));
                out.push_str(&format!("{pad}    {lt} ->\n"));
                block(g, ns, b, ind + 2, out);
            }
            if let Some(d) = &c.default {
                out.push_str(&format!("{pad}    _ ->\n"));
                block(g, ns, d, ind + 2, out);
            }
        }
        _ => out.push_str(&format!("{pad}{}\n", crate::core::show(g, ns, t))),
    }
}
