//! Small functions inlined, and a `match` on their result resolved (SPEC
//! §14): an optimization over erased code (`Ir`), before closure
//! conversion, so that `min x y` at `Int` is a comparison in its caller,
//! and `match xs` with `[]` and `x :: rest` on a known array builds
//! neither the `Some` nor the tuple `uncons` returns. Three rewrites, each
//! giving exactly the results, failures and effects (and their order) of
//! the code it replaces:
//!
//! 1. **Inlining.** A call, with all its arguments, of a definition's
//!    function that is not recursive (it reaches no call of itself,
//!    through any definitions) and small gets that function's body, each
//!    argument bound by a `let`, in order: each is computed once, before
//!    the body, as the call computed them. An argument that is a variable
//!    or a literal is substituted (computing one does nothing). Small is
//!    measured on the body after its own calls are inlined (each body is
//!    rewritten once, in `done`): at most `CALL_SIZE` nodes anywhere, at
//!    most `MAX_SIZE` where the call is a `match`'s scrutinee.
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

/// The largest body inlined where its call is a `match`'s scrutinee:
/// nodes of erased code, after the calls in it are inlined (each variable,
/// literal, call, constructor, operation, `let` and `match` counts one; a
/// mark of whose code it is, none). An array's `uncons` is 18.
pub const MAX_SIZE: usize = 40;

/// The largest body inlined at any other call: `if x <= y then x else y`
/// is 6, a call of two arguments 4.
pub const CALL_SIZE: usize = 12;

/// How deep the rewriting goes again inside code it inlined, where an
/// argument is a constructor it may resolve.
const MAX_DEPTH: usize = 4;

type Owner = Option<DefId>;

pub struct Inliner<'a> {
    /// Each definition's erased code, as `ir::Compiler` made it.
    pub code: &'a HashMap<u32, Arc<Ir>>,
    /// Which definitions are recursive, as found so far.
    pub recursive: &'a mut HashMap<u32, bool>,
    /// Each definition's code after this rewriting, as far as computed.
    pub done: &'a mut HashMap<u32, Arc<Ir>>,
    /// The definition whose code each definition's is: itself, or the one
    /// a specialized copy copies (`spec`), which a runtime error names.
    pub origin: &'a dyn Fn(u32) -> u32,
}

impl Inliner<'_> {
    /// `ir`, the code of `owner` (or of no definition), rewritten.
    pub fn program(&mut self, ir: &Ir, owner: Owner) -> Ir {
        self.go(ir, &Sub::default(), owner, 0)
    }

    /// Definition `d`'s code, rewritten (once).
    pub fn definition(&mut self, d: u32) -> Option<Arc<Ir>> {
        if let Some(x) = self.done.get(&d) {
            return Some(x.clone());
        }
        let code = self.code.get(&d)?.clone();
        let out = Arc::new(self.go(&code, &Sub::default(), Some(DefId((self.origin)(d))), 0));
        self.done.insert(d, out.clone());
        Some(out)
    }

    /// `ir`, rewritten, with its variables as `sub` has them.
    fn go(&mut self, ir: &Ir, sub: &Sub, here: Owner, depth: usize) -> Ir {
        match ir {
            Ir::Var(i) => sub.var(*i),
            Ir::Let(v, b) => {
                let v = self.go(v, sub, here, depth);
                // A variable or literal: substituted, as the body is rewritten.
                if is_atom(&v) {
                    return self.go(b, &sub.put(Arc::new(v)), here, depth);
                }
                let b = self.go(b, &sub.keep(1), here, depth);
                // `let x = e in match x`, `x` used nowhere else: `match e`.
                if let Ir::Case(x, c) = &b {
                    if matches!(**x, Ir::Var(0)) && !case_uses(c, 0) {
                        return self.case(v, lower_case(c), here, depth);
                    }
                }
                bind(Arc::new(v), b)
            }
            Ir::At(o, x) => at(*o, self.go(x, sub, *o, depth)),
            Ir::Case(s, c) => {
                let s = self.go(s, sub, here, depth);
                let mut a = |x: &Arc<Ir>, n: usize| Arc::new(self.go(x, &sub.keep(n), here, depth));
                let c = IrCase {
                    branches: c.branches.iter().map(|(con, n, b)| (*con, *n, a(b, *n))).collect(),
                    lits: c.lits.iter().map(|(l, b)| (l.clone(), a(b, 0))).collect(),
                    default: c.default.as_ref().map(|d| a(d, 0)),
                };
                self.case(s, c, here, depth)
            }
            Ir::Call(..) => {
                let call = ir.map_subterms(|x, k| self.go(x, &sub.keep(k), here, depth));
                self.inline(&call, CALL_SIZE, here, depth).unwrap_or(call)
            }
            _ => ir.map_subterms(|x, k| self.go(x, &sub.keep(k), here, depth)),
        }
    }

    /// `match s` with the (rewritten) arms `c`, in code of `here`.
    fn case(&mut self, s: Ir, c: IrCase, here: Owner, depth: usize) -> Ir {
        let s = self.inline(&s, MAX_SIZE, here, depth).unwrap_or(s);
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

    /// The (rewritten) call `s`, in code of `here`, with the body of the
    /// function it calls with all its arguments bound to them, if that
    /// function is not recursive and its body, rewritten, is at most
    /// `limit` nodes.
    fn inline(&mut self, s: &Ir, limit: usize, here: Owner, depth: usize) -> Option<Ir> {
        let Ir::Call(h, args) = s else { return None };
        let Ir::Global(f) = &**h else { return None };
        let code = self.code.get(&f.0)?;
        if lambdas(code).0 != args.len() || args.is_empty() || self.is_recursive(f.0) {
            return None;
        }
        // Not recursive: rewriting it doesn't come back here.
        let code = self.definition(f.0)?;
        let (_, body) = lambdas(&code);
        if size(body, limit + 1) > limit {
            return None;
        }
        // The body's variables are its parameters, the first outermost:
        // bound by `let`s in the same order, each under the ones before.
        let mut out = at(Some(DefId((self.origin)(f.0))), clone(body));
        for (k, x) in args.iter().enumerate().rev() {
            out = bind(Arc::new(shift(x, k, 0)), out);
        }
        // A constructor passed in may now meet a `match` on it.
        if depth < MAX_DEPTH && args.iter().any(|x| is_con(x)) {
            out = self.go(&out, &Sub::default(), here, depth + 1);
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

/// What the variables of code being rewritten (`Inliner::go`) are in the
/// code it gives: for each binder inside the code it started at, innermost
/// first, the binder it keeps, or the variable or literal put in for it.
/// Putting one in is O(1): each variable is looked up as it is met, so code
/// of n nested `let`s is rewritten in time in proportion to n, not n² as
/// substituting each into its body was.
#[derive(Clone, Default)]
struct Sub {
    binders: crate::pvec::PVec<Bound>,
    /// How many of them are kept.
    kept: usize,
}

#[derive(Clone)]
enum Bound {
    /// Kept, as the given binder (counted from the outermost kept).
    Kept(usize),
    /// Gone: this atom, over the first `n` kept binders.
    Put(Arc<Ir>, usize),
}

impl Sub {
    /// What variable `i` is.
    fn var(&self, i: usize) -> Ir {
        match self.binders.len().checked_sub(i + 1).and_then(|l| self.binders.get(l)) {
            Some(Bound::Kept(l)) => Ir::Var(self.kept - 1 - l),
            Some(Bound::Put(v, n)) => shift(v, self.kept - n, 0),
            // Outside the code rewritten: past the binders kept.
            None => Ir::Var(i - self.binders.len() + self.kept),
        }
    }

    /// Under `n` more binders, kept.
    fn keep(&self, n: usize) -> Sub {
        let mut s = self.clone();
        for _ in 0..n {
            s.binders.push(Bound::Kept(s.kept));
            s.kept += 1;
        }
        s
    }

    /// Under one more binder, with `v` (over the binders kept) put in for it.
    fn put(&self, v: Arc<Ir>) -> Sub {
        let mut binders = self.binders.clone();
        binders.push(Bound::Put(v, self.kept));
        Sub { binders, kept: self.kept }
    }
}

/// How many lambdas code starts with, and what is under them.
fn lambdas(ir: &Ir) -> (usize, &Ir) {
    let mut n = 0;
    let mut body = ir;
    while let Ir::Lam(_, b) = body {
        n += 1;
        body = b;
    }
    (n, body)
}

/// Whether `x` is a constructor applied to its fields.
fn is_con(x: &Ir) -> bool {
    match x {
        Ir::At(_, x) => is_con(x),
        Ir::Con(..) => true,
        Ir::Static(v, id) => super::lower::Static::open_con(v, *id).is_some(),
        _ => false,
    }
}

/// Whether pushing a `match` into `s` can do anything.
fn pushable(s: &Ir) -> bool {
    match s {
        Ir::At(_, x) => pushable(x),
        Ir::Let(..) | Ir::Case(..) | Ir::Con(..) => true,
        Ir::Static(v, id) => super::lower::Static::open_con(v, *id).is_some(),
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
        // Static data: the constructor it is, one level.
        Ir::Static(v, id) => match super::lower::Static::open_con(v, *id) {
            Some((con, fields)) => push(&Ir::Con(con, fields), src, c, here, cases, ctx),
            None => residual(s, src, c, here, ctx),
        },
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

/// `x` as code of `o`. Variables, literals, code already marked, and code
/// that can't fail (so has no error to name) need no mark: a comparison
/// stays one that code generation sees as giving a `Bool`. A lambda's body
/// may fail, so code with one keeps its mark.
pub fn at(o: Owner, x: Ir) -> Ir {
    match x {
        Ir::Var(_) | Ir::Global(_) | Ir::Erased | Ir::Lit(_) | Ir::ConFn(_) | Ir::At(..) => x,
        x if pure(&x, &|_, _| false) && !has_lambda(&x) => x,
        x => Ir::At(o, Arc::new(x)),
    }
}

fn has_lambda(ir: &Ir) -> bool {
    matches!(ir, Ir::Lam(..)) || ir.subterms().iter().any(|(x, _)| has_lambda(x))
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

/// The number of nodes of `ir` (a mark of whose code it is counts none),
/// counting up to `limit`.
pub fn size(ir: &Ir, limit: usize) -> usize {
    let mut n = usize::from(!matches!(ir, Ir::At(..)));
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

/// How many `let`s and markers a `let` is moved past, at most: moving
/// renames the code it passes.
const MAX_FLOAT: usize = 16;

/// `ir` with each `let` whose value computes nothing that can fail or be
/// seen (`pure`) moved into the one branch of a `match` after it that uses
/// it, past the `let`s before that `match` (SPEC §14). The value is then
/// computed only where it is needed, and after the other branch's last use
/// of what it reads: `rest` of `x :: rest` (a slice of the array) is made
/// where the array may be used for the last time, so the array is unshared
/// there and the slice is moved forward in place. Nothing it moves can
/// fail or be seen, so the results, failures and effects are those of the
/// code it rewrites. `pure_call(d, n)`: whether calling definition `d`
/// with `n` arguments is such a value.
pub fn float_in(ir: &Ir, pure_call: &dyn Fn(DefId, usize) -> bool) -> Ir {
    match ir {
        Ir::Let(v, b) => {
            let v = float_in(v, pure_call);
            let b = float_in(b, pure_call);
            // `let x = v in x` is `v`, so a call there is a tail call.
            if matches!(b, Ir::Var(0)) {
                return v;
            }
            if pure(&v, pure_call) {
                if let Some(out) = sink(&v, &b, MAX_FLOAT) {
                    return out;
                }
            }
            Ir::Let(Arc::new(v), Arc::new(b))
        }
        _ => ir.map_subterms(|x, _| float_in(x, pure_call)),
    }
}

/// Code that computes a value and nothing else, and can't fail: no
/// division, indexing, `Nat` subtraction, call of a function (unless
/// `pure_call` says so), or definition's value (a constant computed on
/// first use).
fn pure(ir: &Ir, pure_call: &dyn Fn(DefId, usize) -> bool) -> bool {
    use super::ir::Op;
    match ir {
        Ir::Var(_) | Ir::Erased | Ir::Lit(_) | Ir::ConFn(_) | Ir::Lam(..) => true,
        Ir::Tuple(xs) | Ir::Con(_, xs) => xs.iter().all(|x| pure(x, pure_call)),
        Ir::Proj(x, ..) | Ir::Field(x, _) | Ir::At(_, x) => pure(x, pure_call),
        Ir::Prim(op, xs, nat) => {
            let safe = match op {
                Op::Add | Op::Mul | Op::Neg | Op::Eq | Op::Ne | Op::Lt | Op::Le | Op::Gt | Op::Ge | Op::Len | Op::Concat | Op::TypeApply => true,
                Op::Sub => !nat,
                Op::Div | Op::Rem | Op::Index | Op::Par | Op::When => false,
            };
            safe && xs.iter().all(|x| pure(x, pure_call))
        }
        Ir::Call(h, xs) => matches!(&**h, Ir::Global(d) if pure_call(*d, xs.len())) && xs.iter().all(|x| pure(x, pure_call)),
        _ => false,
    }
}

/// `let v in b`, with the `let` moved into `b` as far as it goes; `None`
/// if it stays where it is.
fn sink(v: &Ir, b: &Ir, fuel: usize) -> Option<Ir> {
    if fuel == 0 {
        return None;
    }
    match b {
        Ir::At(o, x) => sink(v, x, fuel - 1).map(|x| Ir::At(*o, Arc::new(x))),
        // `let x = v in let y = w in e`, `w` not using `x`: `let y = w in
        // let x = v in e`.
        Ir::Let(w, e) if !uses(w, 0) => {
            let w = rename(w, &|i| i - 1);
            let v = rename(v, &|i| i + 1);
            let e = rename(e, &|i| match i {
                0 => 1,
                1 => 0,
                i => i,
            });
            // Only if it then reaches a `match` it goes into.
            let inner = sink(&v, &e, fuel - 1)?;
            Some(Ir::Let(Arc::new(w), Arc::new(inner)))
        }
        Ir::Case(s, c) if !uses(s, 0) => {
            let users = c.branches.iter().filter(|(_, n, x)| uses(x, *n)).count()
                + c.lits.iter().filter(|(_, x)| uses(x, 0)).count()
                + c.default.iter().filter(|x| uses(x, 0)).count();
            if users != 1 {
                return None;
            }
            // In an arm binding `n` fields, `v`'s variable is `n`; the arm
            // that uses it gets the `let`, first, under its fields.
            let arm = |x: &Ir, n: usize| -> Arc<Ir> {
                if uses(x, n) {
                    let body = rename(x, &|i| match i {
                        i if i < n => i + 1,
                        i if i == n => 0,
                        i => i,
                    });
                    let v = rename(v, &|i| i + n);
                    Arc::new(Ir::Let(Arc::new(v), Arc::new(body)))
                } else {
                    Arc::new(rename(x, &|i| if i < n { i } else { i - 1 }))
                }
            };
            Some(Ir::Case(
                Arc::new(rename(s, &|i| i - 1)),
                Arc::new(IrCase {
                    branches: c.branches.iter().map(|(con, n, x)| (*con, *n, arm(x, *n))).collect(),
                    lits: c.lits.iter().map(|(l, x)| (l.clone(), arm(x, 0))).collect(),
                    default: c.default.as_ref().map(|x| arm(x, 0)),
                }),
            ))
        }
        _ => None,
    }
}

/// `ir` with each free variable `i` renamed to `f(i)`.
fn rename(ir: &Ir, f: &dyn Fn(usize) -> usize) -> Ir {
    fn go(ir: &Ir, f: &dyn Fn(usize) -> usize, depth: usize) -> Ir {
        match ir {
            Ir::Var(i) if *i >= depth => Ir::Var(f(i - depth) + depth),
            _ => ir.map_subterms(|x, n| go(x, f, depth + n)),
        }
    }
    go(ir, f, 0)
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
        let mut done = HashMap::new();
        Inliner { code: &code, recursive: &mut rec, done: &mut done, origin: &|d| d }.program(ir, None)
    }

    fn run_with(code: &HashMap<u32, Arc<Ir>>, ir: &Ir) -> Ir {
        let mut rec = HashMap::new();
        let mut done = HashMap::new();
        Inliner { code, recursive: &mut rec, done: &mut done, origin: &|d| d }.program(ir, None)
    }

    fn calls(ir: &Ir) -> usize {
        count(ir, &|x| matches!(x, Ir::Call(..)))
    }

    /// `\x y -> if x <= y then x else y`.
    fn min() -> Arc<Ir> {
        let le = Ir::Prim(super::super::ir::Op::Le, vec![a(Ir::Var(1)), a(Ir::Var(0))], false);
        let body = Ir::Case(a(le), Arc::new(IrCase { branches: vec![(FALSE, 0, a(Ir::Var(0))), (TRUE, 0, a(Ir::Var(1)))], lits: vec![], default: None }));
        a(Ir::Lam(None, a(Ir::Lam(None, a(body)))))
    }

    /// `min v0 v1 + 1`: the call, not a `match`'s scrutinee, is inlined,
    /// and so is a call of a function calling it.
    #[test]
    fn inlines_a_call_anywhere() {
        let mut code = HashMap::new();
        code.insert(0, min());
        // `\x y -> min x y`
        code.insert(1, a(Ir::Lam(None, a(Ir::Lam(None, a(Ir::Call(a(Ir::Global(DefId(0))), vec![a(Ir::Var(1)), a(Ir::Var(0))])))))));
        let add1 = |f: u32| Ir::Prim(super::super::ir::Op::Add, vec![a(Ir::Call(a(Ir::Global(DefId(f))), vec![a(Ir::Var(0)), a(Ir::Var(1))])), a(Ir::Lit(Lit::Num(1)))], false);
        for f in [0, 1] {
            let out = run_with(&code, &add1(f));
            assert_eq!(calls(&out), 0);
            assert_eq!(count(&out, &|x| matches!(x, Ir::Case(..))), 1);
        }
    }

    /// A recursive function, and one too large outside a `match`, stay calls.
    #[test]
    fn leaves_recursive_and_large_calls() {
        let mut code = HashMap::new();
        // `\x -> f x`, calling itself.
        code.insert(0, a(Ir::Lam(None, a(Ir::Call(a(Ir::Global(DefId(0))), vec![a(Ir::Var(0))])))));
        // `\x -> x + x + … + x`, larger than `CALL_SIZE`.
        let mut big = Ir::Var(0);
        for _ in 0..CALL_SIZE {
            big = Ir::Prim(super::super::ir::Op::Add, vec![a(big), a(Ir::Var(0))], false);
        }
        code.insert(1, a(Ir::Lam(None, a(big))));
        for f in [0, 1] {
            let call = Ir::Call(a(Ir::Global(DefId(f))), vec![a(Ir::Var(0))]);
            assert_eq!(calls(&run_with(&code, &call)), 1);
        }
    }

    /// `match (if v0 then None else Some (v0, v1))` with `None -> "none"` and
    /// `Some p -> p.0`: each branch of the `if` picks its arm; no
    /// constructor or tuple is built.
    #[test]
    fn resolves_known_constructors() {
        let inner = Ir::Case(
            a(Ir::Var(0)),
            Arc::new(IrCase {
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
            Arc::new(IrCase { branches: vec![(NONE, 0, a(s("none"))), (SOME, 1, a(Ir::Proj(a(Ir::Var(0)), 0, false)))], lits: vec![], default: None }),
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
            Arc::new(IrCase {
                branches: vec![(FALSE, 0, a(Ir::Con(SOME, vec![a(Ir::Lit(Lit::Num(1)))]))), (TRUE, 0, a(Ir::Var(1)))],
                lits: vec![],
                default: None,
            }),
        );
        let outer = Ir::Case(a(inner), Arc::new(IrCase { branches: vec![(NONE, 0, a(s("none"))), (SOME, 1, a(s("some")))], lits: vec![], default: None }));
        let out = run(&outer);
        assert_eq!(count(&out, &|x| matches!(x, Ir::Lit(Lit::Str(_)))), 2);
        let Ir::Case(scrut, _) = &out else { panic!("the outer `match` stays") };
        assert!(matches!(&**scrut, Ir::Case(..)));
    }
}

