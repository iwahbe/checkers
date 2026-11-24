//! Specialization by dictionary and by function (SPEC §14): an optimization over core
//! terms, applied as `ir::Compiler` erases a call. A call of a definition's
//! function that passes a known instance's dictionary (built by an
//! instance, maybe from other known instances through its context: `Ord
//! (List Int)` from `Ord Int`), with no variables in it, calls a copy of
//! the function in which that parameter is that dictionary. The copy's
//! class functions are then at a known instance, so `ir` calls the
//! instance's functions directly, and its own calls passing the dictionary
//! on are specialized in turn. The call's closed erased arguments (types,
//! proofs) are put into the copy too, so that a dictionary built from them
//! inside it has no variables either.
//!
//! The copy keeps every parameter, so a call passes the same arguments in
//! the same order; those put into the copy are passed as nothing. Building
//! a dictionary computes nothing but the dictionary, so the copy gives
//! exactly the results, failures and effects of the call it replaces. A
//! runtime error in it names the function it copies.
//!
//! A call passing a known function (`known_fn`: a lambda, or a definition's
//! function applied to fewer arguments than it takes, each computing
//! nothing) gets a copy in the same way, in which that parameter is the
//! function: its calls there are direct calls (a lambda applied is compiled
//! as `let`s), whose results come back as their parts (`unbox`), and its
//! calls passing it on are specialized in turn. The function's free
//! variables become parameters of the copy, after the arguments it is made
//! for, and the call passes them; so one copy serves every call passing
//! the same function, and recursion passing it on (`fix`'s `self`) reuses
//! it. A lambda's body is marked as code of the definition it is written
//! in (`AT`), so that a runtime error in it names that definition wherever
//! its code is copied. `ir` substitutes a known function for a `let` or a
//! lambda's parameter bound to it, so that it stays known.
//!
//! Code growth is bounded: one copy per function and arguments put into
//! it (memoized, so recursion and mutual recursion reuse the copy), each
//! such argument at most `MAX_ARG` nodes, copies made inside copies at
//! most `MAX_DEPTH` deep, and at most `MAX_COPIES` copies in a program.
//! Past a bound the call is compiled as it was, reading the dictionary.
//! `CHECKERS_NO_SPEC=1` turns specialization off, to measure it.

use crate::core::{max_var, DefId, Globals, Mult, Tm};
use std::collections::HashMap;
use std::rc::Rc;

/// The largest argument put into a copy: nodes of its term. A dictionary
/// growing at each call (polymorphic recursion) stops being specialized.
pub const MAX_ARG: usize = 64;

/// How deep copies are made inside copies.
pub const MAX_DEPTH: usize = 16;

/// The most copies in a program.
pub const MAX_COPIES: usize = 4096;

/// A function's copy: the function, its body with the arguments put in,
/// and how deep in copies it was made.
pub struct Copy {
    pub of: DefId,
    pub body: Tm,
    pub depth: usize,
}

/// The copies made so far; copy `i` is definition `base + i`.
pub struct Specs {
    pub base: u32,
    memo: HashMap<String, u32>,
    pub copies: Vec<Copy>,
}

impl Specs {
    pub fn new(base: u32) -> Specs {
        Specs { base, memo: HashMap::new(), copies: Vec::new() }
    }

    /// The copy definition `d` is, if it is one.
    pub fn copy(&self, d: u32) -> Option<&Copy> {
        d.checked_sub(self.base).and_then(|i| self.copies.get(i as usize))
    }

    /// The definition whose code `d` is: itself, or the one it copies.
    pub fn origin(&self, d: u32) -> u32 {
        self.copy(d).map_or(d, |c| c.of.0)
    }
}

/// Where a `Compiler` makes copies: the table, staged bodies, and how deep
/// in copies the code being compiled is.
#[derive(Clone, Copy)]
pub struct SpecCx<'a> {
    pub table: &'a std::cell::RefCell<Specs>,
    pub staged: Option<&'a crate::stage::Staged>,
    pub depth: usize,
}

/// Nodes of `t`, counting up to `limit + 1`.
fn size(t: &Tm, limit: usize) -> usize {
    let mut n = 1;
    t.any_sub(|x, _| {
        n += size(x, limit - n.min(limit));
        n > limit
    });
    n
}

/// A dictionary built by instances' functions from types and other such
/// dictionaries, with no variables: a known instance's.
fn closed_dict(g: &Globals, t: &Tm) -> bool {
    fn known(g: &Globals, t: &Tm) -> bool {
        match t.spine() {
            (Tm::Def(b), args) if g.well_known.dict_fns.contains(b) => {
                let mut built = g.defs.get(b.0 as usize).and_then(|i| i.body.as_ref());
                args.iter().all(|a| match built {
                    Some(Tm::Lam(_, m, _, x)) => {
                        built = Some(x);
                        *m == Mult::Zero || known(g, a)
                    }
                    _ => false,
                })
            }
            _ => false,
        }
    }
    max_var(t).is_none() && size(t, MAX_ARG) <= MAX_ARG && known(g, t)
}

/// A call's copy: the copy, which arguments it has put in (passed as
/// nothing), and the variables of the functions put in, passed to it as
/// parameters of their own after the first `at` arguments.
pub struct Spec {
    pub id: DefId,
    pub put: Vec<bool>,
    pub at: usize,
    pub caps: Vec<usize>,
}

/// The name of the `let` marking code of definition `d` (its value,
/// `Tm::Def(d)`, or `Tm::Error` for none) put into another's copy: a
/// lambda's body, so that a runtime error in it names `d` (`ir`).
pub const AT: &str = "\u{0}at";

/// The marked code: `Some(o)` if `t` is a marker `let`, with its body.
pub fn marked(t: &Tm) -> Option<(Option<DefId>, &Tm)> {
    match t {
        Tm::Let(x, Mult::Zero, _, v, b) if &**x == AT => Some((if let Tm::Def(d) = **v { Some(d) } else { None }, b)),
        _ => None,
    }
}

/// A known function with each lambda's body (under all its parameters)
/// marked as code of `owner`, unless it is marked already.
fn mark(t: &Tm, owner: Option<DefId>) -> Tm {
    match t {
        Tm::Lam(..) => mark_body(t, owner),
        Tm::App(f, a, i, m) => Tm::App(Rc::new(mark(f, owner)), Rc::new(mark(a, owner)), *i, *m),
        _ => t.clone(),
    }
}

fn mark_body(t: &Tm, owner: Option<DefId>) -> Tm {
    match t {
        Tm::Lam(x, m, i, b) => Tm::Lam(x.clone(), *m, *i, Rc::new(mark_body(b, owner))),
        _ if marked(t).is_some() => t.clone(),
        _ => Tm::Let(
            AT.into(),
            Mult::Zero,
            Rc::new(Tm::Error),
            Rc::new(owner.map_or(Tm::Error, Tm::Def)),
            Rc::new(crate::core::rename_free(t, 0, &|v| v + 1)),
        ),
    }
}

/// How many parameters `d`'s function takes (its body's lambdas), if it
/// is a function.
fn arity(g: &Globals, staged: Option<&crate::stage::Staged>, d: DefId) -> Option<usize> {
    let body = crate::native::ir::body_of(g, staged, d)?;
    let mut n = 0;
    let mut b = &body;
    while let Tm::Lam(_, _, _, x) = b {
        n += 1;
        b = x;
    }
    (n > 0).then_some(n)
}

/// A known function: a lambda, or a definition's function applied to fewer
/// arguments than it takes, each a variable, a literal, an erased
/// argument, a known dictionary or a known function. Computing one
/// computes nothing but a closure.
pub fn known_fn(g: &Globals, staged: Option<&crate::stage::Staged>, t: &Tm) -> bool {
    let mut args = Vec::new();
    let mut h = t;
    while let Tm::App(f, a, _, m) = h {
        args.push((a, *m));
        h = f;
    }
    match h {
        Tm::Lam(..) => args.is_empty(),
        Tm::Def(d) if !g.well_known.dict_fns.contains(d) => {
            arity(g, staged, *d).is_some_and(|n| args.len() < n)
                && args.iter().all(|(a, m)| {
                    *m == Mult::Zero
                        || matches!(***a, Tm::Var(_) | Tm::Lit(_))
                        || crate::native::ir::known_dict(g, a)
                        || known_fn(g, staged, a)
                })
        }
        _ => false,
    }
}

/// A known function small enough to put into a copy or a `let`'s body.
pub fn small_fn(g: &Globals, staged: Option<&crate::stage::Staged>, t: &Tm) -> bool {
    size(t, MAX_ARG) <= MAX_ARG && known_fn(g, staged, t)
}

fn off() -> bool {
    static OFF: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *OFF.get_or_init(|| std::env::var_os("CHECKERS_NO_SPEC").is_some())
}

/// Whether known functions are substituted for the variables bound to
/// them (`ir`): with specialization, so that they stay known.
pub fn substitutes_fns() -> bool {
    !off()
}

/// The free variables of `t`, each once, in the order they occur.
fn free_in_order(t: &Tm, depth: usize, out: &mut Vec<usize>) {
    match t {
        Tm::Var(v) if *v >= depth => {
            if !out.contains(&(v - depth)) {
                out.push(v - depth);
            }
        }
        _ => t.each_sub(|x, n| free_in_order(x, depth + n, out)),
    }
}

/// The copy of `f` to call with `args` (each with its multiplicity), if
/// one passes a known instance's dictionary or a known function, in code
/// of `owner`.
pub fn specialize(g: &Globals, cx: SpecCx, owner: Option<DefId>, f: DefId, args: &[(&Rc<Tm>, Mult)]) -> Option<Spec> {
    if off() {
        return None;
    }
    let wk = &g.well_known;
    // A class's function at a known instance is a direct call already
    // (`ir`); an instance's dictionary is only built.
    if wk.class_fns.contains(&f) || wk.dict_fns.contains(&f) {
        return None;
    }
    let fun = |a: &Tm| small_fn(g, cx.staged, a);
    if !args.iter().any(|(a, m)| *m != Mult::Zero && (closed_dict(g, a) || fun(a))) {
        return None;
    }
    let body = crate::native::ir::body_of(g, cx.staged, f)?;
    let mut n = 0;
    let mut b = &body;
    while let Tm::Lam(_, _, _, x) = b {
        n += 1;
        b = x;
    }
    let k = n.min(args.len());
    // A function's variables become the copy's parameters after the first
    // `k`: `caps`, the caller's variables, in the order they occur.
    let mut caps = Vec::new();
    let mut pick: Vec<Option<Tm>> = args[..k]
        .iter()
        .map(|(a, m)| match m {
            Mult::Zero => (max_var(a).is_none() && size(a, MAX_ARG) <= MAX_ARG).then(|| (***a).clone()),
            _ if closed_dict(g, a) => Some((***a).clone()),
            _ if fun(a) => {
                free_in_order(a, 0, &mut caps);
                Some(mark(a, owner))
            }
            _ => None,
        })
        .collect();
    if !pick.iter().zip(args).any(|(p, (_, m))| p.is_some() && *m != Mult::Zero) {
        return None;
    }
    // Cap `j` is variable `m - 1 - j` under the copy's `m` parameters for them.
    let m = caps.len();
    for p in pick.iter_mut().flatten() {
        *p = crate::core::rename_free(p, 0, &|v| m - 1 - caps.iter().position(|c| *c == v).unwrap_or(0));
    }
    let key = format!("{}|{}|{:?}", f.0, m, pick);
    let mut t = cx.table.borrow_mut();
    let id = match t.memo.get(&key) {
        Some(id) => *id,
        None => {
            if t.copies.len() >= MAX_COPIES || cx.depth >= MAX_DEPTH {
                return None;
            }
            let id = t.base + t.copies.len() as u32;
            let picked: Vec<Option<&Tm>> = pick.iter().map(Option::as_ref).collect();
            t.copies.push(Copy { of: f, body: put_in(&body, &picked, m, 0), depth: cx.depth + 1 });
            t.memo.insert(key, id);
            id
        }
    };
    Some(Spec { id: DefId(id), put: pick.iter().map(Option::is_some).collect(), at: k, caps })
}

/// `t`, a function's body from its `i`th parameter on, with the picked
/// parameters replaced by their arguments, and `m` parameters for those
/// arguments' variables after them. The parameters stay.
fn put_in(t: &Tm, pick: &[Option<&Tm>], m: usize, i: usize) -> Tm {
    match t {
        Tm::Lam(x, mu, ic, b) if i < pick.len() => Tm::Lam(x.clone(), *mu, *ic, Rc::new(put_in(b, pick, m, i + 1))),
        _ => (0..m).fold(replace(t, pick, m, 0), |b, _| Tm::Lam("cap".into(), Mult::Many, crate::core::Icit::Expl, Rc::new(b))),
    }
}

fn replace(t: &Tm, pick: &[Option<&Tm>], m: usize, depth: usize) -> Tm {
    let k = pick.len();
    match t {
        Tm::Var(v) if *v >= depth && v - depth < k => match pick[k - 1 - (v - depth)] {
            Some(c) => crate::core::rename_free(c, 0, &|x| x + depth),
            None => Tm::Var(v + m),
        },
        Tm::Var(v) if *v >= depth => Tm::Var(v + m),
        _ => t.map_sub(|x, n| replace(x, pick, m, depth + n)),
    }
}
