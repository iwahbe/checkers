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
//! The copy doesn't take the parameters put into it (unless it uses one as
//! a value, `keeps`, or that would leave it none), and a call doesn't pass
//! them: a type or a dictionary put in costs nothing at run time. Building
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
//! its code is copied. A `let` or a lambda's parameter bound to a known
//! function stays known (`known`): `ir` calls the function where the
//! variable is called and makes the copy for it where it is passed, and
//! uses the variable, its one closure, anywhere else. A copy keeps a
//! parameter it uses as a value in that way too (`keeps`): the call
//! passes the closure as well. Such a variable inside a function put into
//! a copy is replaced by its function unless the copy uses it as a value
//! (`settle`), so the caller isn't made to build its closure.
//!
//! A literal or a value known at compile time (§8.9) passed to a function
//! is put into a copy too, so the code using it is computed when compiling
//! (`fold`). That is done where the call is folded (`specialize_folded`),
//! so an argument that becomes static data only once the code around it
//! is folded (`list.length [1, 2, 3]`) is put in as a literal is, into
//! the same copy. The copy is the callee's erased code with the static
//! arguments put in (`Body::Folded`), inlined and folded in turn like any
//! other definition's, so a call in it passing such a value on gets its
//! copy as well: specialization and folding reach a fixed point, within
//! the bounds below. A copy's call of the function it copies passing a
//! value computed from the one put in (`n - 1`) calls the general function
//! (or a copy made already for that value), so recursion on a known value
//! makes one copy, not one per step.
//!
//! Code growth is bounded: one copy per function and arguments put into
//! it (memoized, so recursion and mutual recursion reuse the copy), each
//! such argument at most `MAX_ARG` nodes, copies made inside copies at
//! most `MAX_DEPTH` deep, and at most `MAX_COPIES` copies in a program.
//! Past a bound the call is compiled as it was, reading the dictionary.
//! `CHECKERS_NO_SPEC=1` turns specialization off, to measure it.

use crate::core::{max_var, DefId, Globals, Mult, Tm};
use crate::native::ir::Ir;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

/// The largest argument put into a copy: nodes of its term. A dictionary
/// growing at each call (polymorphic recursion) stops being specialized.
pub const MAX_ARG: usize = 64;

/// How deep copies are made inside copies.
pub const MAX_DEPTH: usize = 16;

/// The most copies in a program.
pub const MAX_COPIES: usize = 4096;

/// A function's copy: the function, its body with the arguments put in,
/// and how deep in copies it was made.
#[derive(Clone)]
pub struct Copy {
    pub of: DefId,
    pub body: Body,
    pub depth: usize,
    /// For each parameter of the copy, the binder of `of` it is (`None`:
    /// one for a variable of a function put in).
    pub binders: Vec<Option<usize>>,
    /// The definition a runtime error in its code names: `of`, unless that
    /// is private to another package than the program's (`report`).
    pub owner: Option<DefId>,
}

/// A copy's code.
#[derive(Clone)]
pub enum Body {
    /// A core term, compiled as the function's body is: made where a call
    /// is erased.
    Term(Tm),
    /// Erased code: that of definition `from` (a copy itself, maybe) with
    /// the static data `put` (one per parameter, `None` for those the copy
    /// takes) in place of its parameters, made where a call is folded.
    Folded { from: u32, put: Vec<Option<Arc<Ir>>>, code: Arc<Ir> },
}

/// The copies made so far; copy `i` is definition `base + i`.
pub struct Specs {
    pub base: u32,
    memo: HashMap<String, u32>,
    pub copies: Vec<Copy>,
    /// Whether a function's parameter is used as a value (`kept`).
    kept: HashMap<(u32, usize), bool>,
    /// Whether copies are made for literals and known values (§8.9): for a
    /// program's code, not for code compiled to run when compiling.
    pub for_values: bool,
    /// A mirror of another program's copies (`mirror`): it makes none of
    /// its own, so their numbers stay the other program's.
    pub frozen: bool,
    /// The definitions no runtime error names (`Globals::hidden`), as the
    /// program was when this table was made.
    hidden: std::collections::HashSet<u32>,
}

impl Specs {
    pub fn new(base: u32, hidden: std::collections::HashSet<u32>) -> Specs {
        Specs { base, memo: HashMap::new(), copies: Vec::new(), kept: HashMap::new(), for_values: false, frozen: false, hidden }
    }

    /// The copy definition `d` is, if it is one.
    pub fn copy(&self, d: u32) -> Option<&Copy> {
        d.checked_sub(self.base).and_then(|i| self.copies.get(i as usize))
    }

    /// Take on the copies of `other` made since the last call: this
    /// table's become a frozen mirror of its.
    pub fn mirror(&mut self, other: &Specs) {
        self.frozen = true;
        self.copies.extend(other.copies[self.copies.len().min(other.copies.len())..].iter().cloned());
    }

    /// The definition whose code `d` is: itself, or the one it copies.
    pub fn origin(&self, d: u32) -> u32 {
        self.copy(d).map_or(d, |c| c.of.0)
    }

    /// The definition a runtime error in `d`'s code names (`None`: no
    /// definition's, as in a `check`).
    pub fn owner(&self, d: u32) -> Option<DefId> {
        self.copy(d).map_or(Some(DefId(d)), |c| c.owner)
    }

    /// Whether `d` is private to another package than the program's, so
    /// that no runtime error names it (§6 rule 9).
    pub fn hidden(&self, d: DefId) -> bool {
        self.hidden.contains(&d.0)
    }
}

/// The function to call for `f` in code whose runtime errors name `owner`:
/// `f`, or if `f` is private to another package than the program's (§6
/// rule 9), its copy whose own runtime errors name `owner` too. In the
/// copy, `f`'s calls of such functions call their copies for `owner` in
/// turn, and its lambdas, and functions put into copies made in it, are
/// code of `owner` (`ir::Compiler::owner`). So a runtime error names the
/// function the program can refer to whose call led to it: the one its
/// own code called, of the package `f` is in. One copy per function and
/// owner (memoized): recursion uses the copy.
pub fn report(g: &Globals, cx: SpecCx, owner: Option<DefId>, f: DefId) -> DefId {
    let mut t = cx.table.borrow_mut();
    if !t.hidden(f) || t.frozen {
        return f;
    }
    let key = format!("report|{}|{:?}", f.0, owner.map(|o| o.0));
    if let Some(id) = t.memo.get(&key) {
        return DefId(*id);
    }
    // A builtin has no code of its own: its errors name its caller already.
    let Some(body) = crate::native::ir::body_of(g, cx.staged, f) else { return f };
    let mut n = 0;
    let mut b = &body;
    while let Tm::Lam(_, _, _, x) = b {
        n += 1;
        b = x;
    }
    let id = t.base + t.copies.len() as u32;
    t.copies.push(Copy { of: f, body: Body::Term(body), depth: cx.depth, binders: (0..n).map(Some).collect(), owner });
    t.memo.insert(key, id);
    DefId(id)
}

/// Where a `Compiler` makes copies: the table, staged bodies, and how deep
/// in copies the code being compiled is.
#[derive(Clone, Copy)]
pub struct SpecCx<'a> {
    pub table: &'a std::cell::RefCell<Specs>,
    pub staged: Option<&'a crate::stage::Staged>,
    pub depth: usize,
}

/// Nodes of `t`, counting up to `limit + 1`. A variable bound to a known
/// function counts as the function, which its calls are.
fn size(t: &Tm, limit: usize) -> usize {
    if let Some((_, f)) = known_var(t) {
        return size(f, limit);
    }
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
/// nothing), which of those it doesn't take (not passed), and the
/// variables of the functions put in, passed to it as parameters of their
/// own after the first `at` arguments.
pub struct Spec {
    pub id: DefId,
    pub put: Vec<bool>,
    pub gone: Vec<bool>,
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

/// The name of the `let` marking a variable bound to a known function:
/// its type is the variable, its value the function (`ir`).
pub const KNOWN: &str = "\u{0}known";

/// Variable `v`, bound to the known function `f`: a call of it calls `f`
/// directly, and a copy is made for `f` where it is passed (`ir`); any
/// other use is the variable, so the closure it holds is built once.
pub fn known(v: Tm, f: Tm) -> Tm {
    Tm::Let(KNOWN.into(), Mult::Zero, Rc::new(v), Rc::new(f), Rc::new(Tm::Error))
}

/// The variable and the function, if `t` is a variable bound to a known
/// function.
pub fn known_var(t: &Tm) -> Option<(&Tm, &Tm)> {
    match t {
        Tm::Let(x, Mult::Zero, v, f, _) if &**x == KNOWN => Some((v, f)),
        _ => None,
    }
}

/// The functions known to be bound to the variables of code being
/// compiled (`ir`): one entry per binder, innermost first. Extending it
/// shares what is there, so code of n nested `let`s is compiled in time
/// and memory in proportion to n.
pub type Fns = crate::pvec::PVec<Option<Rc<Bound>>>;

/// A variable bound to a known function.
pub struct Bound {
    /// The function, over the variables outside the variable's binder.
    pub f: Tm,
    /// Whether the code compiled so far uses the variable itself, so its
    /// closure is built.
    pub used: std::cell::Cell<bool>,
}

/// `t`, under `depth` binders of code where `fns` is known, with each
/// variable bound to a known function marked as bound to it (`known`).
pub fn know(t: &Tm, fns: &Fns, depth: usize) -> Tm {
    match t {
        Tm::Var(v) if *v >= depth => match (v - depth).checked_add(1).and_then(|k| fns.len().checked_sub(k)).and_then(|l| fns.get(l)) {
            Some(Some(b)) => known(Tm::Var(*v), crate::core::rename_free(&b.f, 0, &|x| x + v + 1)),
            _ => t.clone(),
        },
        _ if known_var(t).is_some() => t.clone(),
        _ => t.map_sub(|x, n| know(x, fns, depth + n)),
    }
}

/// Whether `t` is small enough to be put into a copy or a `let`'s body,
/// whatever its variables are bound to (`know` only makes it larger).
pub fn small(t: &Tm) -> bool {
    size(t, MAX_ARG) <= MAX_ARG
}

/// A known function with each lambda's body (under all its parameters)
/// marked as code of `owner`, unless it is marked already; and each
/// function no runtime error names (`hidden`, `report`), so that the copy
/// calls its copy for `owner`, as the call would have.
fn mark(t: &Tm, owner: Option<DefId>, hidden: &dyn Fn(DefId) -> bool) -> Tm {
    match t {
        Tm::Lam(..) => mark_body(t, owner),
        Tm::Def(d) if hidden(*d) => mark_body(t, owner),
        Tm::App(f, a, i, m) => Tm::App(Rc::new(mark(f, owner, hidden)), Rc::new(mark(a, owner, hidden)), *i, *m),
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
    if let Some((_, f)) = known_var(t) {
        return known_fn(g, staged, f);
    }
    let mut args = Vec::new();
    let mut h = t;
    while let Tm::App(f, a, _, m) = h {
        args.push((a, *m));
        h = f;
    }
    // A function marked as code of the definition it was passed from (`mark`).
    let h = marked(h).map_or(h, |(_, x)| x);
    match h {
        Tm::Lam(..) => args.is_empty(),
        Tm::Def(d) if !g.well_known.dict_fns.contains(d) => {
            arity(g, staged, *d).is_some_and(|n| args.len() < n)
                && args.iter().all(|(a, m)| {
                    *m == Mult::Zero
                        || crate::native::ir::inert(g, a)
                        || crate::native::ir::known_dict(g, a)
                        || known_fn(g, staged, a)
                })
        }
        _ => false,
    }
}

/// A known function small enough to put into a copy or a `let`'s body.
pub fn small_fn(g: &Globals, staged: Option<&crate::stage::Staged>, t: &Tm) -> bool {
    let t = known_var(t).map_or(t, |(_, f)| f);
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
/// of `owner`. A literal or a known value is put in where the call is
/// folded (`specialize_folded`), with the values folding finds.
pub fn specialize(g: &Globals, cx: SpecCx, owner: Option<DefId>, f: DefId, args: &[(&Rc<Tm>, Mult)]) -> Option<Spec> {
    if off() || cx.table.borrow().frozen {
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
    // A function the copy uses as a value is passed to it too (`keeps`).
    let mut caps = Vec::new();
    let mut kept = vec![false; k];
    let mut pick: Vec<Option<Tm>> = args[..k]
        .iter()
        .enumerate()
        .map(|(j, (a, m))| match m {
            Mult::Zero => (max_var(a).is_none() && size(a, MAX_ARG) <= MAX_ARG).then(|| (***a).clone()),
            _ if closed_dict(g, a) => Some((***a).clone()),
            _ if fun(a) => {
                let a = settle(g, cx, known_var(a).map_or(&***a, |(_, f)| f));
                let a = &a;
                free_in_order(a, 0, &mut caps);
                kept[j] = keeps(g, cx, f, j);
                Some(mark(a, owner, &|d| cx.table.borrow().hidden(d)))
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
    // The copy doesn't take the parameters put into it (not kept), and the
    // call doesn't pass them; unless that would leave it no parameters,
    // which would make it a constant.
    let put: Vec<bool> = pick.iter().zip(&kept).map(|(p, kept)| p.is_some() && !kept).collect();
    let mut gone = put.clone();
    if m == 0 && n == k && gone.iter().all(|p| *p) {
        gone[k - 1] = false;
    }
    let mut t = cx.table.borrow_mut();
    // A function no runtime error names: a copy for each owner (`report`).
    let named = if t.hidden(f) { owner } else { Some(f) };
    let key = format!("{}|{}|{:?}|{:?}", f.0, m, pick, named.map(|o| o.0));
    let id = match t.memo.get(&key) {
        Some(id) => *id,
        None => {
            if t.copies.len() >= MAX_COPIES || cx.depth >= MAX_DEPTH {
                return None;
            }
            let id = t.base + t.copies.len() as u32;
            let picked: Vec<Option<&Tm>> = pick.iter().map(Option::as_ref).collect();
            // The parameters not put in, the variables' (`caps`), then those
            // after the first `k`.
            let binders = (0..k).filter(|j| !gone[*j]).map(Some).chain((0..m).map(|_| None)).chain((k..n).map(Some)).collect();
            t.copies.push(Copy { of: f, body: Body::Term(put_in(&body, &picked, &kept, &gone, m)), depth: cx.depth + 1, binders, owner: named });
            t.memo.insert(key, id);
            id
        }
    };
    Some(Spec { id: DefId(id), put, gone, at: k, caps })
}

/// Whether parameter `j` of `f`, given a known function, is used as a
/// value: anywhere but called or passed to a parameter of a definition's
/// function (whose copy is made for it) that is not used as a value in
/// turn. Then `f`'s copy keeps the parameter, the call passes the
/// function's closure, and the copy uses that closure wherever it uses the
/// function as a value, rather than building it again at each use.
fn keeps(g: &Globals, cx: SpecCx, f: DefId, j: usize) -> bool {
    if let Some(k) = cx.table.borrow().kept.get(&(f.0, j)) {
        return *k;
    }
    // Parameters the function is passed on to, each looked at once.
    let mut seen = std::collections::HashSet::new();
    let mut todo = vec![(f, j)];
    let mut kept = false;
    while let Some((h, i)) = todo.pop() {
        if !seen.insert((h, i)) {
            continue;
        }
        let Some(body) = crate::native::ir::body_of(g, cx.staged, h) else {
            kept = true;
            break;
        };
        let mut n = 0;
        let mut b = &body;
        while let Tm::Lam(_, _, _, x) = b {
            n += 1;
            b = x;
        }
        if i >= n || used_as_value(g, cx.staged, b, n - 1 - i, &mut todo) {
            kept = true;
            break;
        }
    }
    cx.table.borrow_mut().kept.insert((f.0, j), kept);
    kept
}

/// A known function put into a copy, with each variable in it bound to a
/// known function (`known`) that it only calls or passes to parameters not
/// used as values replaced by that function: the copy needs no closure for
/// it, so the caller isn't made to keep one.
fn settle(g: &Globals, cx: SpecCx, t: &Tm) -> Tm {
    let un = |a: &Tm| known_var(a).map(|(_, f)| settle(g, cx, f));
    match t {
        Tm::App(..) => {
            let mut args = Vec::new();
            let mut h = t;
            while let Tm::App(f, a, i, m) = h {
                args.push((a, *i, *m));
                h = f;
            }
            args.reverse();
            let wk = &g.well_known;
            let callee = match h {
                Tm::Def(d) if !wk.class_fns.contains(d) && !wk.dict_fns.contains(d) => arity(g, cx.staged, *d).map(|n| (*d, n)),
                _ => None,
            };
            let head = un(h).unwrap_or_else(|| settle(g, cx, h));
            args.iter().enumerate().fold(head, |c, (j, (a, i, m))| {
                let a = match callee {
                    Some((d, n)) if *m != Mult::Zero && j < n && known_var(a).is_some() && !keeps(g, cx, d, j) => un(a).unwrap_or(Tm::Error),
                    _ if known_var(a).is_some() => (***a).clone(),
                    _ => settle(g, cx, a),
                };
                Tm::App(Rc::new(c), Rc::new(a), *i, *m)
            })
        }
        _ if known_var(t).is_some() => t.clone(),
        _ => t.map_sub(|x, _| settle(g, cx, x)),
    }
}

/// Whether variable `v` is used as a value in `t` (`keeps`); the
/// parameters it is passed to are added to `todo`.
fn used_as_value(g: &Globals, staged: Option<&crate::stage::Staged>, t: &Tm, v: usize, todo: &mut Vec<(DefId, usize)>) -> bool {
    match t {
        Tm::Var(x) => *x == v,
        Tm::App(..) => {
            let mut args = Vec::new();
            let mut h = t;
            while let Tm::App(f, a, _, m) = h {
                args.push((a, *m));
                h = f;
            }
            args.reverse();
            let wk = &g.well_known;
            let callee = match h {
                Tm::Def(d) if !wk.class_fns.contains(d) && !wk.dict_fns.contains(d) => arity(g, staged, *d).map(|n| (*d, n)),
                _ => None,
            };
            let is_v = |a: &Tm| matches!(a, Tm::Var(x) if *x == v);
            // A lambda applied binds its parameter to it: as a value.
            if matches!(h, Tm::Lam(..)) && args.iter().any(|(a, _)| is_v(a)) {
                return true;
            }
            if !is_v(h) && used_as_value(g, staged, h, v, todo) {
                return true;
            }
            args.iter().enumerate().any(|(j, (a, m))| match callee {
                _ if *m == Mult::Zero => false,
                Some((d, n)) if j < n && is_v(a) => {
                    todo.push((d, j));
                    false
                }
                _ => used_as_value(g, staged, a, v, todo),
            })
        }
        // An erased `let` (a type, a proof, `AT`) computes nothing.
        Tm::Let(_, Mult::Zero, _, _, b) => used_as_value(g, staged, b, v + 1, todo),
        // Another name for it.
        Tm::Let(_, _, _, x, b) if matches!(**x, Tm::Var(y) if y == v) => {
            used_as_value(g, staged, b, 0, todo) || used_as_value(g, staged, b, v + 1, todo)
        }
        _ => t.any_sub(|x, n| used_as_value(g, staged, x, v + n, todo)),
    }
}

/// `t`, a function's body, with its first `pick.len()` parameters' lambdas
/// left out where `put`, the picked parameters replaced by their
/// arguments, and `m` parameters for those arguments' variables after the
/// first parameters.
fn put_in(t: &Tm, pick: &[Option<&Tm>], kept: &[bool], put: &[bool], m: usize) -> Tm {
    let mut lams = Vec::new();
    let mut b = t;
    for _ in 0..pick.len() {
        let Tm::Lam(x, mu, ic, x_b) = b else { unreachable!("a copy is made for parameters the function takes") };
        lams.push((x.clone(), *mu, *ic));
        b = x_b;
    }
    // Where each of the first parameters is among those the copy takes.
    let mut at = Vec::new();
    let mut r = 0;
    for p in put {
        at.push((!p).then_some(r));
        r += usize::from(!p);
    }
    let body = (0..m).fold(replace(b, pick, kept, &at, r, m, 0), |b, _| Tm::Lam("cap".into(), Mult::Many, crate::core::Icit::Expl, Rc::new(b)));
    lams.into_iter().zip(put).rev().fold(body, |b, ((x, mu, ic), p)| if *p { b } else { Tm::Lam(x, mu, ic, Rc::new(b)) })
}

/// A kept parameter stays, marked as bound to its function (`known`).
/// Parameter `j` the copy takes is its `at[j]`th of `r`, before the `m`
/// parameters for the variables.
fn replace(t: &Tm, pick: &[Option<&Tm>], kept: &[bool], at: &[Option<usize>], r: usize, m: usize, depth: usize) -> Tm {
    let k = pick.len();
    match t {
        Tm::Var(v) if *v >= depth && v - depth < k => {
            let j = k - 1 - (v - depth);
            let var = || Tm::Var(depth + m + r - 1 - at[j].expect("a parameter the copy uses is one it takes"));
            match pick[j] {
                Some(c) if kept[j] => known(var(), crate::core::rename_free(c, 0, &|x| x + depth)),
                Some(c) => crate::core::rename_free(c, 0, &|x| x + depth),
                None => var(),
            }
        }
        Tm::Var(v) if *v >= depth => Tm::Var(v - k + r + m),
        _ => t.map_sub(|x, n| replace(x, pick, kept, at, r, m, depth + n)),
    }
}

/// Nodes of erased code, counting up to `limit + 1`; static data counts as
/// one (a known value, §14).
fn ir_size(ir: &Ir, limit: usize) -> usize {
    let mut n = 1;
    for (x, _) in ir.subterms() {
        if n > limit {
            break;
        }
        n += ir_size(x, limit - n.min(limit));
    }
    n
}

/// A call folded (§8.9): of definition `h`, whose erased code is
/// `code[h]`, with `args`, some of them static data (`static_data`) and
/// some not, in code of definition `here` (`depth` deep in copies of
/// functions, 0 for its own code). The copy of `h` with that data put in,
/// and the arguments the call then passes; `None` where none is made (as
/// for `specialize`, and for a copy's call of the function it copies,
/// which passes values computed from those put in: it calls the general
/// function unless a copy for those values exists already).
#[allow(clippy::too_many_arguments)]
pub fn specialize_folded(
    g: &Globals,
    table: &std::cell::RefCell<Specs>,
    code: &HashMap<u32, Arc<Ir>>,
    here: u32,
    depth: usize,
    h: u32,
    args: &[Arc<Ir>],
    static_data: &dyn Fn(&Ir) -> bool,
    key: &dyn Fn(&Ir) -> Option<String>,
) -> Option<(DefId, Vec<Arc<Ir>>)> {
    let mut t = table.borrow_mut();
    if off() || t.frozen || !t.for_values {
        return None;
    }
    let of = t.origin(h);
    let wk = &g.well_known;
    if wk.class_fns.contains(&DefId(of)) || wk.dict_fns.contains(&DefId(of)) {
        return None;
    }
    let body = code.get(&h)?;
    let mut n = 0;
    let mut b = &**body;
    while let Ir::Lam(_, x) = b {
        n += 1;
        b = x;
    }
    let k = n.min(args.len());
    // What is put in: static data small enough, which a key names.
    let mut put: Vec<Option<(Arc<Ir>, String)>> = args[..k]
        .iter()
        .map(|a| (static_data(a) && ir_size(a, MAX_ARG) <= MAX_ARG).then(|| key(a).map(|s| (a.clone(), s))).flatten())
        .chain((k..n).map(|_| None))
        .collect();
    if !put.iter().flatten().any(|(a, _)| !matches!(**a, Ir::Erased)) {
        return None;
    }
    // A copy that would take no parameters keeps the last, so that it stays
    // a function and isn't made a constant.
    if put.iter().all(Option::is_some) {
        put[n - 1] = None;
    }
    let key = format!("folded|{h}|{}", put.iter().map(|p| p.as_ref().map_or("-", |(_, s)| s)).collect::<Vec<_>>().join("|"));
    let id = match t.memo.get(&key) {
        Some(id) => *id,
        None => {
            // In a copy of `h`'s function (`depth > 0`), a value put in is
            // one computed from those put into it (`n - 1`).
            if (of == here && depth > 0) || t.copies.len() >= MAX_COPIES || depth >= MAX_DEPTH {
                return None;
            }
            let id = t.base + t.copies.len() as u32;
            let put: Vec<Option<Arc<Ir>>> = put.iter().map(|p| p.as_ref().map(|(a, _)| a.clone())).collect();
            let from: Vec<Option<usize>> = match t.copy(h) {
                Some(c) => c.binders.clone(),
                None => (0..n).map(Some).collect(),
            };
            let binders = (0..n).filter(|j| put[*j].is_none()).map(|j| from.get(j).copied().flatten()).collect();
            let code = Arc::new(put_in_code(body, &put));
            let owner = t.owner(h);
            t.copies.push(Copy { of: DefId(of), body: Body::Folded { from: h, put, code }, depth: depth + 1, binders, owner });
            t.memo.insert(key, id);
            id
        }
    };
    let rest = args.iter().enumerate().filter(|(j, _)| *j >= k || put[*j].is_none()).map(|(_, a)| a.clone()).collect();
    Some((DefId(id), rest))
}

/// Erased code of a function of `put.len()` parameters, with the static
/// data `put` (closed) in place of the parameters it gives, and lambdas
/// for the others, in order.
fn put_in_code(code: &Ir, put: &[Option<Arc<Ir>>]) -> Ir {
    let n = put.len();
    let mut lams = Vec::new();
    let mut b = code;
    for _ in 0..n {
        let Ir::Lam(o, x) = b else { unreachable!("a copy is made for parameters the function takes") };
        lams.push(*o);
        b = x;
    }
    // Where each parameter is among the `r` the copy takes.
    let mut at = Vec::new();
    let mut r = 0;
    for p in put {
        at.push(p.is_none().then_some(r));
        r += usize::from(p.is_none());
    }
    fn go(ir: &Ir, put: &[Option<Arc<Ir>>], at: &[Option<usize>], r: usize, depth: usize) -> Ir {
        let n = put.len();
        match ir {
            Ir::Var(v) if *v >= depth && v - depth < n => {
                let j = n - 1 - (v - depth);
                match (&put[j], at[j]) {
                    (Some(c), _) => crate::native::ir::shift(c, 0, 0),
                    (None, Some(i)) => Ir::Var(depth + r - 1 - i),
                    (None, None) => unreachable!("a parameter not put in is taken"),
                }
            }
            Ir::Var(v) if *v >= depth => Ir::Var(v - n + r),
            _ => ir.map_subterms(|x, k| go(x, put, at, r, depth + k)),
        }
    }
    let body = go(b, put, &at, r, 0);
    lams.into_iter().zip(put).rev().fold(body, |b, (o, p)| if p.is_some() { b } else { Ir::Lam(o, Arc::new(b)) })
}
