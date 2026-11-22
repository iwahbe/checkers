//! A `match` on a small function's result, resolved (SPEC §14): an
//! optimization over erased code (`Ir`), before closure conversion, so
//! that `match xs` with `[]` and `x :: rest` on a known array builds
//! neither the `Some` nor the tuple `uncons` returns. Three rewrites, each
//! giving exactly the results, failures and effects (and their order) of
//! the code it replaces:
//!
//! 1. **Inlining.** A `match` whose scrutinee is a call, with all its
//!    arguments, of a definition's function that is not recursive (it
//!    reaches no call of itself, through any definitions) and small (its
//!    body at most `MAX_SIZE` nodes) gets that body instead, each argument
//!    bound by a `let`, in order: each is computed once, before the body,
//!    as the call computed them. An argument that is a variable or a
//!    literal is substituted (computing one does nothing).
//! 2. **Case of case.** A `match` on a `let`, an `if` or a `match` is
//!    pushed past the `let` and into the branches, but only when no arm of
//!    the outer `match` then appears in more than one place, so no code is
//!    duplicated; otherwise only the `let`s are passed.
//! 3. **Case of known constructor.** A `match` on a constructor applied to
//!    its fields binds them by `let`s, in order, and continues with that
//!    constructor's arm. A `let` of a tuple whose every use is a
//!    projection binds the components instead, so the tuple isn't built.
//!
//! Code that came from another definition is marked with it (`Ir::At`):
//! a runtime error there names that definition, as it did when it was
//! called.

use super::ir::{shift, Ir, IrCase, Lit};
use crate::core::DefId;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// The largest body inlined: nodes of erased code (each variable, literal,
/// call, constructor, operation, `let`, `match` and arm counts one). An
/// array's `uncons` is 18.
pub const MAX_SIZE: usize = 40;

/// How deep inlining goes inside code it inlined.
const MAX_DEPTH: usize = 4;

type Owner = Option<DefId>;

pub struct Inliner<'a> {
    /// Each definition's erased code, as `ir::Compiler` made it.
    pub code: &'a HashMap<u32, Arc<Ir>>,
    /// Which definitions are recursive, as found so far.
    pub recursive: &'a mut HashMap<u32, bool>,
}

impl Inliner<'_> {
    /// `ir`, the code of `owner` (or of no definition), rewritten.
    pub fn program(&mut self, ir: &Ir, owner: Owner) -> Ir {
        self.go(ir, owner, 0)
    }

    fn go(&mut self, ir: &Ir, here: Owner, depth: usize) -> Ir {
        match ir {
            Ir::Let(v, b) => {
                let v = self.go(v, here, depth);
                let b = self.go(b, here, depth);
                // `let x = e in match x`, `x` used nowhere else: `match e`.
                if let Ir::Case(x, c) = &b {
                    if matches!(**x, Ir::Var(0)) && !case_uses(c, 0) {
                        return self.case(v, lower_case(c), here, depth);
                    }
                }
                bind(Arc::new(v), b)
            }
            Ir::At(o, x) => at(*o, self.go(x, *o, depth)),
            Ir::Case(s, c) => {
                let s = self.go(s, here, depth);
                let mut a = |x: &Arc<Ir>| Arc::new(self.go(x, here, depth));
                let c = IrCase {
                    branches: c.branches.iter().map(|(con, n, b)| (*con, *n, a(b))).collect(),
                    lits: c.lits.iter().map(|(l, b)| (l.clone(), a(b))).collect(),
                    default: c.default.as_ref().map(&mut a),
                };
                self.case(s, c, here, depth)
            }
            _ => ir.map_subterms(|x, _| self.go(x, here, depth)),
        }
    }

    /// `match s` with the (rewritten) arms `c`, in code of `here`.
    fn case(&mut self, s: Ir, c: IrCase, here: Owner, depth: usize) -> Ir {
        let s = match self.inline(&s, depth) {
            Some(body) => self.go(&body, here, depth + 1),
            None => s,
        };
        if !c.lits.is_empty() || !pushable(&s) {
            return Ir::Case(Arc::new(s), Arc::new(c));
        }
        let n = c.branches.len() + 1;
        let (ir, uses) = push(&s, here, &c, here, true, here);
        if uses.iter().all(|u| *u <= 1) {
            return ir;
        }
        // An arm would be in two places: pass only the `let`s.
        let (ir, uses) = push(&s, here, &c, here, false, here);
        debug_assert!(uses.len() == n && uses.iter().all(|u| *u <= 1));
        ir
    }

    /// The body of the function `s` calls with all its arguments, bound to
    /// them, if it is inlined.
    fn inline(&mut self, s: &Ir, depth: usize) -> Option<Ir> {
        if depth >= MAX_DEPTH {
            return None;
        }
        let Ir::Call(h, args) = s else { return None };
        let Ir::Global(f) = &**h else { return None };
        let code = self.code.get(&f.0)?;
        let mut n = 0;
        let mut body = &**code;
        while let Ir::Lam(_, b) = body {
            n += 1;
            body = b;
        }
        if n == 0 || n != args.len() || size(body, MAX_SIZE + 1) > MAX_SIZE || self.is_recursive(f.0) {
            return None;
        }
        // The body's variables are its parameters, the first outermost:
        // bound by `let`s in the same order, each under the ones before.
        let mut out = at(Some(*f), clone(body));
        for (k, x) in args.iter().enumerate().rev() {
            out = bind(Arc::new(shift(x, k, 0)), out);
        }
        Some(out)
    }

    /// Whether `f`'s code reaches a call of `f`.
    fn is_recursive(&mut self, f: u32) -> bool {
        if let Some(r) = self.recursive.get(&f) {
            return *r;
        }
        let mut seen = HashSet::new();
        let mut todo = vec![f];
        let mut found = false;
        while let Some(d) = todo.pop() {
            let Some(c) = self.code.get(&d) else { continue };
            let mut gs = Vec::new();
            super::ir::globals_in(c, &mut gs);
            for g in gs {
                if g.0 == f {
                    found = true;
                    break;
                }
                if seen.insert(g.0) {
                    todo.push(g.0);
                }
            }
            if found {
                break;
            }
        }
        self.recursive.insert(f, found);
        found
    }
}

/// Whether pushing a `match` into `s` can do anything.
fn pushable(s: &Ir) -> bool {
    match s {
        Ir::At(_, x) => pushable(x),
        Ir::Let(..) | Ir::Case(..) | Ir::Con(..) => true,
        _ => false,
    }
}

/// `match s` with arms `c` (code of `here`), where `s` is code of `src`,
/// pushed into `s`: past its `let`s, into its branches (with `cases`), and
/// resolved where it meets a constructor; for a place in code of `ctx`.
/// Also how many times each arm (the branches, then the default) appears
/// in the result.
fn push(s: &Ir, src: Owner, c: &IrCase, here: Owner, cases: bool, ctx: Owner) -> (Ir, Vec<usize>) {
    let n = c.branches.len() + 1;
    match s {
        Ir::At(o, x) => push(x, *o, c, here, cases, ctx),
        Ir::Let(v, b) => {
            let (b, uses) = push(b, src, &shift_case(c, 1), here, cases, ctx);
            (bind(Arc::new(at_in(ctx, src, clone(v))), b), uses)
        }
        Ir::Case(s2, c2) if cases => {
            let mut uses = vec![0; n];
            let mut add = |u: Vec<usize>| uses.iter_mut().zip(u).for_each(|(a, b)| *a += b);
            // The inner `match` is `src`'s code; its arms say whose they are.
            let branches = c2
                .branches
                .iter()
                .map(|(con, k, b)| {
                    let (b, u) = push(b, src, &shift_case(c, *k), here, cases, src);
                    add(u);
                    (*con, *k, Arc::new(b))
                })
                .collect();
            let lits = c2
                .lits
                .iter()
                .map(|(l, b)| {
                    let (b, u) = push(b, src, c, here, cases, src);
                    add(u);
                    (l.clone(), Arc::new(b))
                })
                .collect();
            let default = c2.default.as_ref().map(|d| {
                let (b, u) = push(d, src, c, here, cases, src);
                add(u);
                Arc::new(b)
            });
            (at_in(ctx, src, Ir::Case(s2.clone(), Arc::new(IrCase { branches, lits, default }))), uses)
        }
        Ir::Con(con, fields) => {
            let (k, arm) = match c.branches.iter().position(|(b, _, _)| b == con) {
                Some(k) if c.branches[k].1 == fields.len() => (k, c.branches[k].2.clone()),
                Some(_) => return residual(s, src, c, here, ctx),
                // The default binds no fields.
                None => match &c.default {
                    Some(d) => (n - 1, Arc::new(shift(d, fields.len(), 0))),
                    None => return residual(s, src, c, here, ctx),
                },
            };
            // Each field under the ones before it, as the arm sees them.
            let mut out = at_in(ctx, here, clone(&arm));
            for (j, x) in fields.iter().enumerate().rev() {
                out = bind(Arc::new(at_in(ctx, src, shift(x, j, 0))), out);
            }
            let mut uses = vec![0; n];
            uses[k] = 1;
            (out, uses)
        }
        _ => residual(s, src, c, here, ctx),
    }
}

/// `match s` left as it is: each arm once.
fn residual(s: &Ir, src: Owner, c: &IrCase, here: Owner, ctx: Owner) -> (Ir, Vec<usize>) {
    let c = IrCase { branches: c.branches.clone(), lits: c.lits.clone(), default: c.default.clone() };
    let n = c.branches.len() + 1;
    let mut uses = vec![1; n];
    if c.default.is_none() {
        uses[n - 1] = 0;
    }
    (at_in(ctx, here, Ir::Case(Arc::new(at_in(here, src, clone(s))), Arc::new(c))), uses)
}

/// `x`, code of `o`, at a place in code of `ctx`.
fn at_in(ctx: Owner, o: Owner, x: Ir) -> Ir {
    if ctx == o {
        x
    } else {
        at(o, x)
    }
}

/// `x` as code of `o`. Variables, literals and code already marked need no mark.
pub fn at(o: Owner, x: Ir) -> Ir {
    match x {
        Ir::Var(_) | Ir::Global(_) | Ir::Erased | Ir::Lit(_) | Ir::ConFn(_) | Ir::At(..) => x,
        x => Ir::At(o, Arc::new(x)),
    }
}

/// `let v in b`: a variable or literal substituted; a tuple whose every use
/// is a projection bound as its components.
fn bind(v: Arc<Ir>, b: Ir) -> Ir {
    if is_atom(&v) {
        return subst0(&b, &v);
    }
    let (o, inner) = match &*v {
        Ir::At(o, x) => (Some(*o), &**x),
        x => (None, x),
    };
    if let Ir::Tuple(xs) = inner {
        let m = xs.len();
        if m >= 2 && projections_only(&b, 0, m) {
            // Components bound in order; projection `i` is component `i`.
            let mut out = split(&b, m, 0);
            for (j, x) in xs.iter().enumerate().rev() {
                let x = shift(x, j, 0);
                let x = match o {
                    Some(o) => at(o, x),
                    None => x,
                };
                out = bind(Arc::new(x), out);
            }
            return out;
        }
    }
    Ir::Let(v, Arc::new(b))
}

/// Code that does nothing when it runs and is a word: a variable, an
/// erased value, a constructor without fields, a small number. (A definition's value may be a constant
/// computed on first use, which can fail: not an atom.)
fn is_atom(v: &Ir) -> bool {
    match v {
        Ir::Var(_) | Ir::Erased => true,
        Ir::Con(_, xs) => xs.is_empty(),
        Ir::Lit(Lit::Num(n)) => checkers_rt::word::fits(*n),
        _ => false,
    }
}

/// Whether every use of variable `x` in `b` is a projection that a tuple of
/// `m` components gives as one of them: component `i` before the last, or
/// the rest from the last (D174: the last may be a tuple laid out flat).
fn projections_only(b: &Ir, x: usize, m: usize) -> bool {
    match b {
        Ir::Var(i) => *i != x,
        Ir::Proj(e, i, rest) if matches!(&**e, Ir::Var(v) if *v == x) => *rest == (*i + 1 == m) && *i < m,
        _ => b.subterms().iter().all(|(s, k)| projections_only(s, x + k, m)),
    }
}

/// `b`, where variable 0 was a tuple of `m` components, under `m` binders
/// of the components instead: projection `i` is component `i`.
fn split(b: &Ir, m: usize, depth: usize) -> Ir {
    match b {
        Ir::Proj(e, i, _) if matches!(&**e, Ir::Var(v) if *v == depth) => Ir::Var(depth + m - 1 - i),
        Ir::Var(v) if *v > depth => Ir::Var(v + m - 1),
        Ir::Var(v) => Ir::Var(*v),
        // `let x = p.i`: now a variable, substituted.
        Ir::Let(v, body) => bind(Arc::new(split(v, m, depth)), split(body, m, depth + 1)),
        _ => b.map_subterms(|s, k| split(s, m, depth + k)),
    }
}

/// `b` with variable 0 replaced by the atom `v` (seen from outside `b`'s binder).
fn subst0(b: &Ir, v: &Ir) -> Ir {
    fn go(b: &Ir, v: &Ir, depth: usize) -> Ir {
        match b {
            Ir::Var(i) if *i == depth => shift(v, depth, 0),
            Ir::Var(i) if *i > depth => Ir::Var(i - 1),
            Ir::Var(i) => Ir::Var(*i),
            _ => b.map_subterms(|s, k| go(s, v, depth + k)),
        }
    }
    go(b, v, 0)
}

/// Whether an arm of `c` uses variable `x`.
fn case_uses(c: &IrCase, x: usize) -> bool {
    c.branches.iter().any(|(_, n, b)| uses(b, x + n)) || c.lits.iter().any(|(_, b)| uses(b, x)) || c.default.as_ref().is_some_and(|d| uses(d, x))
}

fn uses(ir: &Ir, x: usize) -> bool {
    match ir {
        Ir::Var(i) => *i == x,
        _ => ir.subterms().iter().any(|(s, k)| uses(s, x + k)),
    }
}

/// The arms `c`, which don't use variable 0, without its binder.
fn lower_case(c: &IrCase) -> IrCase {
    let down = |b: &Ir, n: usize| Arc::new(shift_down(b, n));
    IrCase {
        branches: c.branches.iter().map(|(con, n, b)| (*con, *n, down(b, *n))).collect(),
        lits: c.lits.iter().map(|(l, b)| (l.clone(), down(b, 0))).collect(),
        default: c.default.as_ref().map(|d| down(d, 0)),
    }
}

/// `ir` without the binder of variable `depth`, which it doesn't use.
fn shift_down(ir: &Ir, depth: usize) -> Ir {
    match ir {
        Ir::Var(i) if *i > depth => Ir::Var(i - 1),
        Ir::Var(i) => Ir::Var(*i),
        _ => ir.map_subterms(|s, k| shift_down(s, depth + k)),
    }
}

/// The arms `c` under `k` more binders.
fn shift_case(c: &IrCase, k: usize) -> IrCase {
    IrCase {
        branches: c.branches.iter().map(|(con, n, b)| (*con, *n, Arc::new(shift(b, k, *n)))).collect(),
        lits: c.lits.iter().map(|(l, b)| (l.clone(), Arc::new(shift(b, k, 0)))).collect(),
        default: c.default.as_ref().map(|d| Arc::new(shift(d, k, 0))),
    }
}

/// The number of nodes of `ir`, counting up to `limit`.
pub fn size(ir: &Ir, limit: usize) -> usize {
    let mut n = 1;
    for (s, _) in ir.subterms() {
        if n > limit {
            break;
        }
        n += size(s, limit);
    }
    n
}

fn clone(ir: &Ir) -> Ir {
    shift(ir, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::ConId;

    const FALSE: ConId = ConId(0);
    const TRUE: ConId = ConId(1);
    const NONE: ConId = ConId(2);
    const SOME: ConId = ConId(3);

    fn a(x: Ir) -> Arc<Ir> {
        Arc::new(x)
    }

    fn s(x: &str) -> Ir {
        Ir::Lit(Lit::Str(Arc::from(x)))
    }

    fn count(ir: &Ir, p: &dyn Fn(&Ir) -> bool) -> usize {
        p(ir) as usize + ir.subterms().iter().map(|(x, _)| count(x, p)).sum::<usize>()
    }

    fn run(ir: &Ir) -> Ir {
        let code = HashMap::new();
        let mut rec = HashMap::new();
        Inliner { code: &code, recursive: &mut rec }.program(ir, None)
    }

    /// `match (if v0 then None else Some (v0, v1))` with `None -> "none"` and
    /// `Some p -> p.0`: each branch of the `if` picks its arm; no
    /// constructor or tuple is built.
    #[test]
    fn resolves_known_constructors() {
        let inner = Ir::Case(
            a(Ir::Var(0)),
            a(IrCase {
                branches: vec![
                    (FALSE, 0, a(Ir::Con(SOME, vec![a(Ir::Tuple(vec![a(Ir::Prim(super::super::ir::Op::Add, vec![a(Ir::Var(0)), a(Ir::Var(1))], false)), a(Ir::Var(1))]))]))),
                    (TRUE, 0, a(Ir::Con(NONE, vec![]))),
                ],
                lits: vec![],
                default: None,
            }),
        );
        let outer = Ir::Case(
            a(inner),
            a(IrCase { branches: vec![(NONE, 0, a(s("none"))), (SOME, 1, a(Ir::Proj(a(Ir::Var(0)), 0, false)))], lits: vec![], default: None }),
        );
        let out = run(&outer);
        assert_eq!(count(&out, &|x| matches!(x, Ir::Con(..) | Ir::Tuple(_) | Ir::Proj(..))), 0);
        assert_eq!(count(&out, &|x| matches!(x, Ir::Case(..))), 1);
        assert_eq!(count(&out, &|x| matches!(x, Ir::Lit(Lit::Str(_)))), 1);
    }

    /// `match (if v0 then v1 else Some 1)`: the `Some` arm would be in both
    /// branches, so the `match` stays where it is.
    #[test]
    fn leaves_an_arm_in_one_place() {
        let inner = Ir::Case(
            a(Ir::Var(0)),
            a(IrCase {
                branches: vec![(FALSE, 0, a(Ir::Con(SOME, vec![a(Ir::Lit(Lit::Num(1)))]))), (TRUE, 0, a(Ir::Var(1)))],
                lits: vec![],
                default: None,
            }),
        );
        let outer = Ir::Case(a(inner), a(IrCase { branches: vec![(NONE, 0, a(s("none"))), (SOME, 1, a(s("some")))], lits: vec![], default: None }));
        let out = run(&outer);
        assert_eq!(count(&out, &|x| matches!(x, Ir::Lit(Lit::Str(_)))), 2);
        let Ir::Case(scrut, _) = &out else { panic!("the outer `match` stays") };
        assert!(matches!(&**scrut, Ir::Case(..)));
    }
}

