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

use super::lower::*;
use std::collections::BTreeSet;

pub struct Rc<'p> {
    pub next: u32,
    /// Fields per constructor (to match reuse sizes).
    pub fields_of: &'p dyn Fn(u32) -> usize,
}

type Set = BTreeSet<V>;

impl Rc<'_> {
    /// Code for `e` that consumes exactly the variables in `own`.
    pub fn rc(&mut self, e: E, own: Set) -> E {
        let fvs = free_vars(&e);
        let dead: Vec<V> = own.difference(&fvs).copied().collect();
        let own: Set = own.intersection(&fvs).copied().collect();
        let body = self.node(e, own);
        dead.into_iter().rev().fold(body, |acc, x| E::Drop(x, Box::new(acc)))
    }

    /// Children evaluated in order: each owned variable goes to the last
    /// child that uses it; earlier ones borrow it.
    fn children(&mut self, xs: Vec<E>, own: &Set) -> (Vec<V>, Vec<E>) {
        let fvs: Vec<Set> = xs.iter().map(free_vars).collect();
        let mut owns: Vec<Set> = vec![Set::new(); xs.len()];
        for v in own {
            if let Some(k) = fvs.iter().rposition(|s| s.contains(v)) {
                owns[k].insert(*v);
            }
        }
        let out = xs.into_iter().zip(owns).map(|(x, o)| self.rc(x, o)).collect();
        (Vec::new(), out)
    }

    fn with_dups(dups: Vec<V>, e: E) -> E {
        dups.into_iter().rev().fold(e, |acc, v| E::Dup(v, Box::new(acc)))
    }

    fn node(&mut self, e: E, own: Set) -> E {
        match e {
            // A borrowed variable that is kept: one more reference.
            E::Var(x) if !own.contains(&x) => E::Dup(x, Box::new(E::Var(x))),
            E::MkClo { f, captured } => {
                let borrowed: Vec<V> = captured.iter().filter(|v| !own.contains(v)).copied().collect();
                Self::with_dups(borrowed, E::MkClo { f, captured })
            }
            E::Var(_)
            | E::Int(_)
            | E::BigLit(_)
            | E::Str(_)
            | E::Bytes(_)
            | E::Erased
            | E::Unit
            | E::Global(_)
            | E::ConFn(_)
            | E::Fail(_) => e,
            E::Let(x, a, b) => {
                let fa = free_vars(&a);
                let mut fb = free_vars(&b);
                fb.remove(&x);
                // The body runs last: it owns what both use; the value borrows.
                let oa: Set = own.iter().filter(|v| fa.contains(v) && !fb.contains(v)).copied().collect();
                let a2 = self.rc(*a, oa);
                let mut ob: Set = own.intersection(&fb).copied().collect();
                ob.insert(x);
                let b2 = self.rc(*b, ob);
                E::Let(x, Box::new(a2), Box::new(b2))
            }
            E::Call { f, args, tail } => {
                let (dups, args) = self.children(args, &own);
                Self::with_dups(dups, E::Call { f, args, tail })
            }
            E::Apply { f, args, tail } => {
                let mut xs = vec![*f];
                xs.extend(args);
                let (dups, mut xs) = self.children(xs, &own);
                let f = xs.remove(0);
                Self::with_dups(dups, E::Apply { f: Box::new(f), args: xs, tail })
            }
            E::Con { con, fields, reuse } => {
                let mut xs = fields;
                if let Some(r) = reuse {
                    xs.push(E::Var(r));
                }
                let (dups, mut xs) = self.children(xs, &own);
                if reuse.is_some() {
                    xs.pop();
                }
                Self::with_dups(dups, E::Con { con, fields: xs, reuse })
            }
            E::Tuple(xs) => {
                let (dups, xs) = self.children(xs, &own);
                Self::with_dups(dups, E::Tuple(xs))
            }
            E::Par(xs) => {
                let (dups, xs) = self.children(xs, &own);
                Self::with_dups(dups, E::Par(xs))
            }
            E::Borrow { op, args, .. } => E::Borrow { op, args, drops: own.into_iter().collect() },
            E::Case { scrut, arms, lits, default } => {
                let mut arms2 = Vec::new();
                // A borrowed scrutinee is never dropped here.
                let owned = own.contains(&scrut);
                for mut a in arms {
                    let used = free_vars(&a.body).contains(&scrut) || !owned;
                    let n = a.fields.len();
                    let mut own_arm: Set = own.clone();
                    own_arm.extend(a.fields.iter().flatten().copied());
                    let fields_used: Vec<V> = a.fields.iter().flatten().copied().collect();
                    let body = if used {
                        self.rc(a.body, own_arm)
                    } else {
                        own_arm.remove(&scrut);
                        // Reuse the matched value's memory for a constructor of
                        // the same size built in this arm.
                        let tok = if n > 0 && self.place_reuse(&mut a.body, n) { Some(self.next - 1) } else { None };
                        match tok {
                            Some(t) => {
                                own_arm.insert(t);
                                let b = self.rc(a.body, own_arm);
                                E::DropReuse(scrut, t, n, Box::new(b))
                            }
                            None => {
                                let b = self.rc(a.body, own_arm);
                                E::Drop(scrut, Box::new(b))
                            }
                        }
                    };
                    a.body = Self::with_dups(fields_used, body);
                    arms2.push(a);
                }
                let mut lits2 = Vec::new();
                for (l, b) in lits {
                    lits2.push((l, self.rc(b, own.clone())));
                }
                let default = default.map(|d| Box::new(self.rc(*d, own.clone())));
                E::Case { scrut, arms: arms2, lits: lits2, default }
            }
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
                E::Let(_, a, b) => find(b, n, fields_of).or_else(|| find(a, n, fields_of)),
                E::Call { args, .. } | E::Tuple(args) | E::Par(args) => args.iter_mut().find_map(|a| find(a, n, fields_of)),
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

/// Reference counting for a whole function. Its parameters (and, for a
/// lambda, the captured variables, loaded from its closure) are owned.
pub fn function(f: &mut Func, fields_of: &dyn Fn(u32) -> usize) {
    let mut own: Set = f.params.iter().copied().collect();
    if let FnKind::Lambda { captured } = &f.kind {
        own.extend(captured.iter().copied());
    }
    let mut r = Rc { next: f.nvars, fields_of };
    let body = std::mem::replace(&mut f.body, E::Erased);
    f.body = r.rc(body, own);
    f.nvars = r.next;
}
