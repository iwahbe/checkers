//! Reference counting, Perceus style (D74; Reinking et al., PLDI 2021).
//!
//! Every variable a function binds is owned: each path through the code
//! consumes it exactly once. Where several parts of an expression use a
//! variable, the last one to run owns it and the earlier ones borrow it
//! (the owner keeps it alive); a borrowed variable is duplicated only where
//! it is kept (returned, stored, passed to a call). Where a branch doesn't
//! use an owned variable, the branch drops it first. Operations that borrow (`Borrow`) drop what they were
//! the last use of right after. A `match` duplicates the fields its arm uses
//! and drops the value matched on if the arm doesn't use it; when the arm
//! also builds a constructor of the same size, the drop becomes `DropReuse`:
//! if that was the only reference, its memory is built into directly.
//!
//! A definition's function borrows the parameters it only reads and passes
//! on to parameters that are borrowed in turn (`infer_borrowed`, as Lean 4
//! infers them): it neither duplicates nor drops them, and its callers keep
//! the arguments alive over the call, dropping them after it if the call
//! was their last use. A loop passing a value on unchanged then counts it
//! once, not at each step. A closure's code takes every argument owned, so
//! a function that borrows is made a closure of through code that calls it
//! and then drops those arguments (`owned_entry`).

use super::lower::*;
use std::collections::{BTreeSet, HashMap};

pub struct Rc<'p> {
    pub next: u32,
    /// Fields per constructor (to match reuse sizes).
    pub fields_of: &'p dyn Fn(u32) -> usize,
    /// Functions' borrowed parameters (`infer_borrowed`).
    pub borrowed: &'p HashMap<u32, Vec<bool>>,
    /// How many words each function returns.
    pub rets: &'p dyn Fn(u32) -> usize,
}

type Set = BTreeSet<V>;

/// The free variables of an expression and of each part `Rc::node` visits,
/// computed once, bottom-up: asking each node for its subtree's free
/// variables would walk a deeply nested expression once per level.
struct Fv {
    vars: Set,
    /// `Let`: the value and the body (the bound variable still free);
    /// `Call`, `Tuple`, `Par`: the arguments; `Apply`: the function, then
    /// the arguments; `Con`: the fields, then the reused cell; `Case`: the
    /// arms' bodies (their fields still free), the literal arms' bodies,
    /// the default. Other nodes have none.
    parts: Vec<Fv>,
}

impl Fv {
    fn leaf(vars: Set) -> Fv {
        Fv { vars, parts: Vec::new() }
    }

    /// Parts whose free variables are all free in the whole.
    fn of_parts(parts: Vec<Fv>) -> Fv {
        let mut vars = Set::new();
        for p in &parts {
            vars.extend(p.vars.iter().copied());
        }
        Fv { vars, parts }
    }

    fn of(e: &E) -> Fv {
        match e {
            E::Var(v) => Fv::leaf(Set::from([*v])),
            E::Let(x, a, b) => {
                let (a, b) = (Fv::of(a), Fv::of(b));
                let mut vars = a.vars.clone();
                vars.extend(b.vars.iter().filter(|v| *v != x).copied());
                Fv { vars, parts: vec![a, b] }
            }
            E::Call { args, .. } | E::Tuple(args) | E::Par(args) | E::Multi(args) => Fv::of_parts(args.iter().map(Fv::of).collect()),
            E::LetMulti(xs, a, b) => {
                let (a, b) = (Fv::of(a), Fv::of(b));
                let mut vars = a.vars.clone();
                vars.extend(b.vars.iter().filter(|v| !xs.contains(v)).copied());
                Fv { vars, parts: vec![a, b] }
            }
            E::Apply { f, args, .. } => Fv::of_parts(std::iter::once(&**f).chain(args).map(Fv::of).collect()),
            E::Con { fields, reuse, .. } => {
                let mut parts: Vec<Fv> = fields.iter().map(Fv::of).collect();
                if let Some(r) = reuse {
                    parts.push(Fv::leaf(Set::from([*r])));
                }
                Fv::of_parts(parts)
            }
            E::Case { scrut, arms, lits, default } => {
                let mut vars = Set::from([*scrut]);
                let mut parts = Vec::new();
                for a in arms {
                    let p = Fv::of(&a.body);
                    let bound: Set = a.fields.iter().flatten().copied().collect();
                    vars.extend(p.vars.difference(&bound).copied());
                    parts.push(p);
                }
                for (_, b) in lits {
                    let p = Fv::of(b);
                    vars.extend(p.vars.iter().copied());
                    parts.push(p);
                }
                if let Some(d) = default {
                    let p = Fv::of(d);
                    vars.extend(p.vars.iter().copied());
                    parts.push(p);
                }
                Fv { vars, parts }
            }
            E::At(_, b) => {
                let b = Fv::of(b);
                Fv { vars: b.vars.clone(), parts: vec![b] }
            }
            // No parts are visited: atomic arguments, or code the pass made.
            _ => Fv::leaf(free_vars(e)),
        }
    }
}

impl Rc<'_> {
    /// Code for `e` that consumes exactly the variables in `own`; `fv` is
    /// `Fv::of(&e)`.
    fn rc(&mut self, e: E, fv: Fv, own: Set) -> E {
        let dead: Vec<V> = own.difference(&fv.vars).copied().collect();
        let own: Set = own.intersection(&fv.vars).copied().collect();
        let body = self.node(e, fv.parts, own);
        dead.into_iter().rev().fold(body, |acc, x| E::Drop(x, Box::new(acc)))
    }

    /// Children evaluated in order: each owned variable goes to the last
    /// child that uses it; earlier ones borrow it.
    fn children(&mut self, xs: Vec<E>, fvs: Vec<Fv>, own: &Set) -> (Vec<V>, Vec<E>) {
        let mut owns: Vec<Set> = vec![Set::new(); xs.len()];
        for v in own {
            if let Some(k) = fvs.iter().rposition(|s| s.vars.contains(v)) {
                owns[k].insert(*v);
            }
        }
        let out = xs.into_iter().zip(fvs).zip(owns).map(|((x, f), o)| self.rc(x, f, o)).collect();
        (Vec::new(), out)
    }

    fn fresh(&mut self) -> V {
        self.next += 1;
        self.next - 1
    }

    fn with_dups(dups: Vec<V>, e: E) -> E {
        dups.into_iter().rev().fold(e, |acc, v| E::Dup(v, Box::new(acc)))
    }

    fn node(&mut self, e: E, parts: Vec<Fv>, own: Set) -> E {
        let mut parts = parts.into_iter();
        match e {
            // A borrowed variable that is kept: one more reference.
            E::Var(x) if !own.contains(&x) => E::Dup(x, Box::new(E::Var(x))),
            E::MkClo { f, captured } => {
                let borrowed: Vec<V> = captured.iter().filter(|v| !own.contains(v)).copied().collect();
                Self::with_dups(borrowed, E::MkClo { f, captured })
            }
            E::Var(_)
            | E::Int(_)
            | E::Str(_)
            | E::Bytes(_)
            | E::Static(..)
            | E::Erased
            | E::Unit
            | E::Global(_)
            | E::ConFn(_)
            | E::Fail(_) => e,
            E::Let(x, a, b) => {
                let (fa, fb) = (parts.next().unwrap(), parts.next().unwrap());
                // The body runs last: it owns what both use; the value borrows.
                let in_b = |v: &V| *v != x && fb.vars.contains(v);
                let oa: Set = own.iter().filter(|v| fa.vars.contains(v) && !in_b(v)).copied().collect();
                let mut ob: Set = own.iter().filter(|v| in_b(v)).copied().collect();
                ob.insert(x);
                let a2 = self.rc(*a, fa, oa);
                let b2 = self.rc(*b, fb, ob);
                E::Let(x, Box::new(a2), Box::new(b2))
            }
            E::LetMulti(xs, a, b) => {
                let (fa, fb) = (parts.next().unwrap(), parts.next().unwrap());
                // As `Let`, binding several variables.
                let in_b = |v: &V| !xs.contains(v) && fb.vars.contains(v);
                let oa: Set = own.iter().filter(|v| fa.vars.contains(v) && !in_b(v)).copied().collect();
                let mut ob: Set = own.iter().filter(|v| in_b(v)).copied().collect();
                ob.extend(xs.iter().copied());
                let a2 = self.rc(*a, fa, oa);
                let b2 = self.rc(*b, fb, ob);
                E::LetMulti(xs, Box::new(a2), Box::new(b2))
            }
            E::Multi(xs) => {
                let (dups, xs) = self.children(xs, parts.collect(), &own);
                Self::with_dups(dups, E::Multi(xs))
            }
            E::Call { f, args, tail } => {
                let Some(b) = self.borrowed.get(&f) else {
                    let (dups, args) = self.children(args, parts.collect(), &own);
                    return Self::with_dups(dups, E::Call { f, args, tail });
                };
                // An argument passed to a borrowed parameter (a variable,
                // or a word that isn't counted: `name_borrowed_args`) is
                // kept alive over the call, and dropped after it if it is
                // owned here; the others are passed owned, as to any call.
                let held: Set = args.iter().zip(b).filter(|(_, b)| **b).filter_map(|(a, _)| if let E::Var(x) = a { Some(*x) } else { None }).collect();
                let rest: Set = own.difference(&held).copied().collect();
                let after: Vec<V> = own.intersection(&held).copied().collect();
                let mut args: Vec<Option<E>> = args.into_iter().map(Some).collect();
                let (mut xs, mut fvs, mut at) = (Vec::new(), Vec::new(), Vec::new());
                for (j, fv) in parts.enumerate() {
                    if !b[j] {
                        xs.push(args[j].take().unwrap());
                        fvs.push(fv);
                        at.push(j);
                    }
                }
                let (dups, xs) = self.children(xs, fvs, &rest);
                for (j, x) in at.into_iter().zip(xs) {
                    args[j] = Some(x);
                }
                let call = Self::with_dups(dups, E::Call { f, args: args.into_iter().map(Option::unwrap).collect(), tail: tail && after.is_empty() });
                if after.is_empty() {
                    return call;
                }
                // The call's result, then the drops.
                let n = (self.rets)(f);
                let rs: Vec<V> = (0..n).map(|_| self.fresh()).collect();
                let result = if n == 1 { E::Var(rs[0]) } else { E::Multi(rs.iter().map(|r| E::Var(*r)).collect()) };
                let body = after.into_iter().rev().fold(result, |acc, x| E::Drop(x, Box::new(acc)));
                if n == 1 {
                    E::Let(rs[0], Box::new(call), Box::new(body))
                } else {
                    E::LetMulti(rs, Box::new(call), Box::new(body))
                }
            }
            E::Apply { f, args, tail } => {
                let mut xs = vec![*f];
                xs.extend(args);
                let (dups, mut xs) = self.children(xs, parts.collect(), &own);
                let f = xs.remove(0);
                Self::with_dups(dups, E::Apply { f: Box::new(f), args: xs, tail })
            }
            E::Con { con, fields, reuse } => {
                let mut xs = fields;
                if let Some(r) = reuse {
                    xs.push(E::Var(r));
                }
                let (dups, mut xs) = self.children(xs, parts.collect(), &own);
                if reuse.is_some() {
                    xs.pop();
                }
                Self::with_dups(dups, E::Con { con, fields: xs, reuse })
            }
            E::Tuple(xs) => {
                let (dups, xs) = self.children(xs, parts.collect(), &own);
                Self::with_dups(dups, E::Tuple(xs))
            }
            E::Par(xs) => {
                let (dups, xs) = self.children(xs, parts.collect(), &own);
                Self::with_dups(dups, E::Par(xs))
            }
            E::Borrow { op, args, .. } => E::Borrow { op, args, drops: own.into_iter().collect() },
            E::Case { scrut, arms, lits, default } => {
                let mut arms2 = Vec::new();
                // A borrowed scrutinee is never dropped here.
                let owned = own.contains(&scrut);
                for mut a in arms {
                    let fv = parts.next().unwrap();
                    let used = fv.vars.contains(&scrut) || !owned;
                    let n = a.fields.len();
                    let mut own_arm: Set = own.clone();
                    own_arm.extend(a.fields.iter().flatten().copied());
                    let fields_used: Vec<V> = a.fields.iter().flatten().copied().collect();
                    let body = if used {
                        self.rc(a.body, fv, own_arm)
                    } else {
                        own_arm.remove(&scrut);
                        // Reuse the matched value's memory for a constructor of
                        // the same size built in this arm.
                        let tok = if n > 0 && self.place_reuse(&mut a.body, n) { Some(self.next - 1) } else { None };
                        match tok {
                            Some(t) => {
                                own_arm.insert(t);
                                // The cell is a new free variable on the way to the constructor.
                                let fv = Fv::of(&a.body);
                                let b = self.rc(a.body, fv, own_arm);
                                E::DropReuse(scrut, t, n, Box::new(b))
                            }
                            None => {
                                let b = self.rc(a.body, fv, own_arm);
                                E::Drop(scrut, Box::new(b))
                            }
                        }
                    };
                    a.body = Self::with_dups(fields_used, body);
                    arms2.push(a);
                }
                let mut lits2 = Vec::new();
                for (l, b) in lits {
                    let fv = parts.next().unwrap();
                    lits2.push((l, self.rc(b, fv, own.clone())));
                }
                let default = default.map(|d| Box::new(self.rc(*d, parts.next().unwrap(), own.clone())));
                E::Case { scrut, arms: arms2, lits: lits2, default }
            }
            E::At(o, b) => E::At(o, Box::new(self.rc(*b, parts.next().unwrap(), own))),
            E::Dup(..) | E::Drop(..) | E::DropReuse(..) => e,
        }
    }

    /// Mark one constructor of `n` fields in `e` to be built in a reused
    /// cell; true if there was one (its token is the newest variable).
    fn place_reuse(&mut self, e: &mut E, n: usize) -> bool {
        fn find<'a>(e: &'a mut E, n: usize, fields_of: &dyn Fn(u32) -> usize) -> Option<&'a mut Option<V>> {
            match e {
                E::Con { con, fields, reuse } => {
                    if reuse.is_none() && fields.len() == n && fields_of(*con) == n {
                        // Prefer an inner one: the fields are built first.
                        let inner = fields.iter_mut().find_map(|f| find(f, n, fields_of));
                        return match inner {
                            Some(r) => Some(r),
                            None => Some(reuse),
                        };
                    }
                    fields.iter_mut().find_map(|f| find(f, n, fields_of))
                }
                E::Let(_, a, b) | E::LetMulti(_, a, b) => find(b, n, fields_of).or_else(|| find(a, n, fields_of)),
                E::At(_, b) => find(b, n, fields_of),
                E::Call { args, .. } | E::Tuple(args) | E::Par(args) | E::Multi(args) => args.iter_mut().find_map(|a| find(a, n, fields_of)),
                E::Apply { f, args, .. } => args.iter_mut().find_map(|a| find(a, n, fields_of)).or_else(|| find(f, n, fields_of)),
                E::Case { arms, lits, default, .. } => {
                    // Only in one place: a cell can be reused once.
                    if let Some(r) = arms.iter_mut().find_map(|a| find(&mut a.body, n, fields_of)) {
                        return Some(r);
                    }
                    if let Some(r) = lits.iter_mut().find_map(|(_, b)| find(b, n, fields_of)) {
                        return Some(r);
                    }
                    default.as_mut().and_then(|d| find(d, n, fields_of))
                }
                _ => None,
            }
        }
        let fields_of = self.fields_of;
        let tok = self.next;
        match find(e, n, fields_of) {
            Some(slot) => {
                *slot = Some(tok);
                self.next += 1;
                true
            }
            None => false,
        }
    }
}

/// Reference counting for function `i`. Its parameters (and, for a
/// lambda, the captured variables, loaded from its closure) are owned, but
/// for those it borrows (`infer_borrowed`).
pub fn function(i: u32, f: &mut Func, fields_of: &dyn Fn(u32) -> usize, borrowed: &HashMap<u32, Vec<bool>>, rets: &dyn Fn(u32) -> usize) {
    let mine = borrowed.get(&i);
    let mut own: Set = f.params.iter().enumerate().filter(|(j, _)| !mine.is_some_and(|b| b[*j])).map(|(_, v)| *v).collect();
    if let FnKind::Lambda { captured } = &f.kind {
        own.extend(captured.iter().copied());
    }
    let mut next = f.nvars;
    let body = name_borrowed_args(std::mem::replace(&mut f.body, E::Erased), borrowed, &mut next);
    let mut r = Rc { next, fields_of, borrowed, rets };
    let fv = Fv::of(&body);
    f.body = r.rc(body, fv, own);
    f.nvars = r.next;
}

/// Which parameters of the functions from `from` on are borrowed (Perceus's
/// borrowing, as Lean 4 infers it): their callers keep the arguments alive
/// over the call and drop them after, so the function neither duplicates
/// what it only reads nor drops it. A definition's function borrows a
/// parameter unless it may consume it: return it, store it, capture it,
/// bind it to another name, pass it to a parameter that isn't borrowed,
/// give it to `++` on the left (which appends in place to what it owns), or
/// match on it in an arm that could build in its memory (reuse). A tail
/// call to a function of the same recursive group passing it a value the
/// caller owns makes that parameter owned too, so that the call stays a
/// tail call (a loop): the caller would have to drop the value after it.
/// Lambdas, wrappers and constants own their parameters. `known` holds what
/// was inferred for earlier functions; the new ones are added to it.
pub fn infer_borrowed(funcs: &[Func], from: usize, known: &mut HashMap<u32, Vec<bool>>, fields_of: &dyn Fn(u32) -> usize) {
    let new: Vec<usize> = (from..funcs.len()).filter(|i| matches!(funcs[*i].kind, FnKind::Global) && !funcs[*i].params.is_empty()).collect();
    for i in &new {
        known.insert(*i as u32, vec![true; funcs[*i].params.len()]);
    }
    // Recursive groups among the new functions.
    let index: HashMap<usize, usize> = new.iter().enumerate().map(|(k, i)| (*i, k)).collect();
    let edges: Vec<Vec<usize>> = new
        .iter()
        .map(|i| {
            let mut out = Vec::new();
            calls(&funcs[*i].body, &mut |f| {
                if let Some(k) = index.get(&(f as usize)) {
                    out.push(*k);
                }
            });
            out
        })
        .collect();
    let mut group = vec![0; new.len()];
    for (g, scc) in crate::elab::order::sccs(&edges).into_iter().enumerate() {
        for k in scc {
            group[k] = g;
        }
    }
    let group_of = |f: u32| index.get(&(f as usize)).map(|k| group[*k]);
    // Parameters only become owned, so this ends.
    loop {
        let mut changed = false;
        for (k, i) in new.iter().enumerate() {
            let f = &funcs[*i];
            let mine = known[&(*i as u32)].clone();
            let borrowed: Set = f.params.iter().zip(&mine).filter(|(_, b)| **b).map(|(v, _)| *v).collect();
            let mut owned = Set::new();
            let mut theirs = Vec::new();
            let mut cx = Uses { known, fields_of, borrowed: &borrowed, owned: &mut owned, theirs: &mut theirs, group: group[k], group_of: &group_of };
            cx.walk(&f.body);
            let mut set = |f: u32, j: usize| {
                if let Some(b) = known.get_mut(&f) {
                    if b[j] {
                        b[j] = false;
                        changed = true;
                    }
                }
            };
            for (j, v) in f.params.iter().enumerate() {
                if mine[j] && owned.contains(v) {
                    set(*i as u32, j);
                }
            }
            for (g, j) in theirs {
                set(g, j);
            }
        }
        if !changed {
            break;
        }
    }
    for i in &new {
        if known[&(*i as u32)].iter().all(|b| !b) {
            known.remove(&(*i as u32));
        }
    }
}

/// The functions `e` calls directly.
fn calls(e: &E, out: &mut dyn FnMut(u32)) {
    if let E::Call { f, .. } = e {
        out(*f);
    }
    each_sub(e, &mut |x| calls(x, out));
}

/// The expressions directly inside `e`.
fn each_sub(e: &E, f: &mut dyn FnMut(&E)) {
    match e {
        E::Let(_, a, b) | E::LetMulti(_, a, b) => {
            f(a);
            f(b);
        }
        E::Call { args, .. } | E::Tuple(args) | E::Par(args) | E::Multi(args) | E::Borrow { args, .. } => args.iter().for_each(f),
        E::Apply { f: h, args, .. } => {
            f(h);
            args.iter().for_each(f);
        }
        E::Con { fields, .. } => fields.iter().for_each(f),
        E::Case { arms, lits, default, .. } => {
            arms.iter().for_each(|a| f(&a.body));
            for (l, b) in lits {
                f(l);
                f(b);
            }
            if let Some(d) = default {
                f(d);
            }
        }
        E::At(_, b) | E::Dup(_, b) | E::Drop(_, b) | E::DropReuse(_, _, _, b) => f(b),
        _ => {}
    }
}

/// How a function's body uses its borrowed parameters (`infer_borrowed`).
struct Uses<'a> {
    known: &'a HashMap<u32, Vec<bool>>,
    fields_of: &'a dyn Fn(u32) -> usize,
    borrowed: &'a Set,
    /// Parameters the body may consume.
    owned: &'a mut Set,
    /// Other functions' parameters a tail call needs owned.
    theirs: &'a mut Vec<(u32, usize)>,
    group: usize,
    group_of: &'a dyn Fn(u32) -> Option<usize>,
}

impl Uses<'_> {
    fn walk(&mut self, e: &E) {
        match e {
            E::Var(x) => {
                self.owned.insert(*x);
            }
            E::MkClo { captured, .. } => self.owned.extend(captured.iter().copied()),
            E::Call { f, args, tail } => {
                let b = self.known.get(f);
                for (j, a) in args.iter().enumerate() {
                    let to_borrowed = b.is_some_and(|b| b[j]);
                    // Anything but a parameter this function borrows (or a
                    // word that isn't counted) is the caller's to drop.
                    if to_borrowed && *tail && (self.group_of)(*f) == Some(self.group) {
                        let passed_on = matches!(a, E::Var(x) if self.borrowed.contains(x));
                        if !passed_on && !matches!(a, E::Int(_) | E::Erased | E::Unit) {
                            self.theirs.push((*f, j));
                        }
                    }
                    match a {
                        E::Var(_) if to_borrowed => {}
                        _ => self.walk(a),
                    }
                }
            }
            // `++` appends in place to a left side it owns (D74).
            E::Borrow { op: BOp::Prim(super::ir::Op::Concat, _), args, .. } => {
                if let Some(E::Var(x)) = args.first() {
                    self.owned.insert(*x);
                }
            }
            E::Borrow { .. } => {}
            E::Case { scrut, arms, .. } => {
                // An arm not using the value may build in its memory.
                if arms.iter().any(|a| {
                    let n = a.fields.len();
                    n > 0 && !free_vars(&a.body).contains(scrut) && builds(&a.body, n, self.fields_of)
                }) {
                    self.owned.insert(*scrut);
                }
                each_sub(e, &mut |x| self.walk(x));
            }
            _ => each_sub(e, &mut |x| self.walk(x)),
        }
    }
}

/// Whether `e` builds a constructor of `n` fields (one a matched value's
/// memory could be reused for, `place_reuse`).
fn builds(e: &E, n: usize, fields_of: &dyn Fn(u32) -> usize) -> bool {
    if let E::Con { con, fields, .. } = e {
        if fields.len() == n && fields_of(*con) == n {
            return true;
        }
    }
    let mut found = false;
    each_sub(e, &mut |x| found = found || builds(x, n, fields_of));
    found
}

/// `e` with each argument a call passes to a borrowed parameter a variable:
/// where one isn't, the call's arguments that compute something are bound
/// to variables first, in order, so that the caller can drop the value
/// after the call (`Rc::node`).
pub fn name_borrowed_args(e: E, known: &HashMap<u32, Vec<bool>>, next: &mut u32) -> E {
    let e = map_sub(e, &mut |x| name_borrowed_args(x, known, next));
    match e {
        E::Call { f, args, tail } if known.get(&f).is_some_and(|b| args.iter().zip(b).any(|(a, b)| *b && !held(a))) => {
            let mut lets = Vec::new();
            let args: Vec<E> = args
                .into_iter()
                .map(|a| match a {
                    _ if held(&a) => a,
                    _ => {
                        let v = *next;
                        *next += 1;
                        lets.push((v, a));
                        E::Var(v)
                    }
                })
                .collect();
            lets.into_iter().rev().fold(E::Call { f, args, tail }, |b, (v, a)| E::Let(v, Box::new(a), Box::new(b)))
        }
        e => e,
    }
}

/// `e` with `f` applied to the expressions directly inside it.
fn map_sub(e: E, f: &mut dyn FnMut(E) -> E) -> E {
    let all = |xs: Vec<E>, f: &mut dyn FnMut(E) -> E| xs.into_iter().map(&mut *f).collect::<Vec<E>>();
    match e {
        E::Let(x, a, b) => E::Let(x, Box::new(f(*a)), Box::new(f(*b))),
        E::LetMulti(xs, a, b) => E::LetMulti(xs, Box::new(f(*a)), Box::new(f(*b))),
        E::Call { f: g, args, tail } => E::Call { f: g, args: all(args, f), tail },
        E::Tuple(xs) => E::Tuple(all(xs, f)),
        E::Par(xs) => E::Par(all(xs, f)),
        E::Multi(xs) => E::Multi(all(xs, f)),
        E::Borrow { op, args, drops } => E::Borrow { op, args: all(args, f), drops },
        E::Apply { f: h, args, tail } => E::Apply { f: Box::new(f(*h)), args: all(args, f), tail },
        E::Con { con, fields, reuse } => E::Con { con, fields: all(fields, f), reuse },
        E::Case { scrut, arms, lits, default } => E::Case {
            scrut,
            arms: arms.into_iter().map(|a| Arm { body: f(a.body), ..a }).collect(),
            lits: lits.into_iter().map(|(l, b)| (f(l), f(b))).collect(),
            default: default.map(|d| Box::new(f(*d))),
        },
        E::At(o, b) => E::At(o, Box::new(f(*b))),
        E::Dup(v, b) => E::Dup(v, Box::new(f(*b))),
        E::Drop(v, b) => E::Drop(v, Box::new(f(*b))),
        E::DropReuse(v, t, n, b) => E::DropReuse(v, t, n, Box::new(f(*b))),
        e => e,
    }
}

/// An argument a caller can pass to a borrowed parameter as it is: a
/// variable it keeps alive over the call, or a word that isn't counted.
fn held(a: &E) -> bool {
    matches!(a, E::Var(_) | E::Int(_) | E::Erased | E::Unit)
}


/// Function `i`, which borrows the parameters `b` marks, as code taking
/// all its arguments owned: it calls `i` and then drops those (a closure's
/// code, `Program::entries`).
pub fn owned_entry(i: u32, f: &Func, b: &[bool]) -> Func {
    let n = f.params.len() as u32;
    let params: Vec<V> = (0..n).collect();
    let call = E::Call { f: i, args: params.iter().map(|v| E::Var(*v)).collect(), tail: false };
    let rs: Vec<V> = (n..n + f.rets as u32).collect();
    let result = if f.rets == 1 { E::Var(rs[0]) } else { E::Multi(rs.iter().map(|r| E::Var(*r)).collect()) };
    let drops = params.iter().zip(b).filter(|(_, b)| **b).rev().fold(result, |acc, (v, _)| E::Drop(*v, Box::new(acc)));
    let body = if f.rets == 1 { E::Let(rs[0], Box::new(call), Box::new(drops)) } else { E::LetMulti(rs.clone(), Box::new(call), Box::new(drops)) };
    let bounds = f.params.iter().zip(&params).filter_map(|(v, w)| Some((*w, *f.bounds.get(v)?))).collect();
    Func { name: f.name.clone(), owner: f.owner, kind: FnKind::Global, params, body, nvars: n + f.rets as u32, rets: f.rets, bounds }
}

/// `e` with each variable bound to another variable (`let x = y`, as
/// `tailrec` writes for a loop's next values) replaced by that variable:
/// so that a parameter passed on unchanged is seen to be.
pub fn forward_aliases(e: E) -> E {
    match e {
        E::Let(x, a, b) if matches!(*a, E::Var(_)) => {
            let E::Var(y) = *a else { unreachable!() };
            forward_aliases(rename(*b, x, y))
        }
        e => map_sub(e, &mut forward_aliases),
    }
}

/// `e` with variable `x` renamed `y` (variables are bound once in a
/// function, so nothing in `e` binds `y`).
fn rename(e: E, x: V, y: V) -> E {
    let r = |v: V| if v == x { y } else { v };
    match e {
        E::Var(v) => E::Var(r(v)),
        E::MkClo { f, captured } => E::MkClo { f, captured: captured.into_iter().map(r).collect() },
        E::Case { scrut, arms, lits, default } => map_sub(E::Case { scrut: r(scrut), arms, lits, default }, &mut |e| rename(e, x, y)),
        E::Con { con, fields, reuse } => map_sub(E::Con { con, fields, reuse: reuse.map(r) }, &mut |e| rename(e, x, y)),
        E::Borrow { op, args, drops } => map_sub(E::Borrow { op, args, drops: drops.into_iter().map(r).collect() }, &mut |e| rename(e, x, y)),
        e => map_sub(e, &mut |e| rename(e, x, y)),
    }
}

/// The definitions `e` uses as values (`E::Global`) and the functions it
/// makes closures of (`E::MkClo`).
pub fn closures_in(e: &E, values: &mut Vec<u32>, closures: &mut Vec<u32>) {
    match e {
        E::Global(d) => values.push(*d),
        E::MkClo { f, .. } => closures.push(*f),
        // The definitions' functions static data holds, as closures.
        E::Static(v, id) => {
            for x in v.reachable(*id) {
                match v.node(x) {
                    SNode::Global(d) => values.push(*d),
                    SNode::Code(f) => closures.push(*f),
                    _ => {}
                }
            }
        }
        _ => each_sub(e, &mut |x| closures_in(x, values, closures)),
    }
}
