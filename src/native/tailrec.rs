//! Recursion made tail recursion (SPEC §14): an optimization over
//! closure-converted code, before reference counting, so that a function
//! whose recursive call is followed by a little work runs in constant stack.
//! It runs after proofs and gives exactly the results the code it replaces
//! gives, failures and their order included.
//!
//! A definition's function `f` qualifies when every path that ends in a
//! call of `f` itself has one of two shapes, and at least one path does:
//!
//! - **A constructor around the call** (`n :: f (n - 1)`; "tail recursion
//!   modulo cons"). `f.dps xs dest i` computes `f xs` and stores it in field
//!   `i` of the cell `dest`. At such a path `f` builds the cell with the field
//!   empty and calls `f.dps` to fill it; `f.dps` does the same, storing each
//!   new cell into the previous one, and calls itself in tail position. The
//!   cell with the empty field is new, held only by the code that fills it
//!   (its count is at least two until then, so nothing reuses it), and
//!   reaches no other code before it is complete. Fields after the call must
//!   be atoms (they run after the call today, and atoms do nothing).
//! - **An associative operator on the call and an atom** (`n + f (n - 1)`).
//!   Only built-in operators that are associative for every value, and only
//!   where accumulating costs no more than the recursion it replaces. The
//!   other operand must be an atom, already computed before the call, so
//!   nothing runs in a different order.
//!   - `+` and `*` (on `Int` and `Nat`, which have no fixed size;
//!     commutative, so the call may be on either side): `f.acc xs acc`
//!     computes `acc ⊕ f xs`, passing `acc ⊕ n` on in tail position.
//!   - `++` with the call on the left (`f xs ++ s`): `f.acc xs acc`
//!     computes `f xs ++` what `acc` holds, passing `s` put in front of
//!     `acc` on (`BOp::ConcatPush`), and at the base case appends `acc` to
//!     its value (`BOp::ConcatAll`). How depends on what `++` copies, which
//!     the value's representation, and so its type, decides (code generic
//!     in the type has the same representations): a list's `++` copies only
//!     its left side, so `acc` is the list, `s ++ acc` copying just `s`; a
//!     string's, bytes' or array's copies both, so `s ++ acc` would copy the
//!     growing value at each step, and `acc` is a list of the pieces instead,
//!     appended at the end in one new value, each element copied once. With
//!     the call on the right the pieces would come in the result's order,
//!     but that is not rewritten.

use super::lower::*;
use crate::native::ir::Op;

/// Rewrite the definitions' functions in `funcs[from..]`, adding helpers.
/// `nil` is the empty list's constructor, which `f.acc` for `++` starts
/// with; without it, `++` isn't rewritten.
pub fn program(funcs: &mut Vec<Func>, from: usize, nil: Option<u32>) {
    let end = funcs.len();
    for i in from..end {
        if !matches!(funcs[i].kind, FnKind::Global) || funcs[i].params.is_empty() || funcs[i].params.len() + 2 > MAX_ARITY {
            continue;
        }
        let me = i as u32;
        let mut s = Scan::default();
        scan(&funcs[i].body, me, &mut s);
        if s.cons == 0 && s.acc.is_empty() || s.cons > 0 && !s.acc.is_empty() {
            continue;
        }
        let helper = funcs.len() as u32;
        if s.cons > 0 {
            dps(funcs, i, helper);
        } else if let Some(mode) = acc_mode(&s.acc, nil) {
            acc(funcs, i, helper, mode);
        }
    }
}

/// What a function's tail positions hold.
#[derive(Default)]
struct Scan {
    /// Operator paths: the operation, and whether the call is its left operand.
    acc: Vec<(BOp, bool)>,
    /// Constructor paths.
    cons: usize,
}

/// An expression that does nothing when it runs: its value is ready.
fn atom(e: &E) -> bool {
    matches!(e, E::Var(_) | E::Int(_) | E::BigLit(_) | E::Str(_) | E::Bytes(_) | E::Static(_) | E::Erased | E::Unit | E::ConFn(_))
}

fn is_self(e: &E, me: u32) -> bool {
    matches!(e, E::Call { f, .. } if *f == me)
}

/// `let r = f args in x ⊕ r` (or `r ⊕ x`): the operation and whether the
/// call is on the left.
fn op_path(r: V, a: &E, b: &E, me: u32) -> Option<(BOp, bool)> {
    if !is_self(a, me) {
        return None;
    }
    let E::Borrow { op: op @ BOp::Prim(p, _), args, .. } = b else { return None };
    if !matches!(p, Op::Add | Op::Mul | Op::Concat) || args.len() != 2 {
        return None;
    }
    let is_r = |e: &E| matches!(e, E::Var(v) if *v == r);
    match (&args[0], &args[1]) {
        (x, y) if is_r(y) && atom(x) && !is_r(x) => Some((*op, false)),
        (x, y) if is_r(x) && atom(y) && !is_r(y) => Some((*op, true)),
        _ => None,
    }
}

/// A constructor with a call of `me` as a field and only atoms after it:
/// that field.
fn con_path(e: &E, me: u32) -> Option<usize> {
    let E::Con { fields, reuse: None, .. } = e else { return None };
    let k = fields.iter().rposition(|x| is_self(x, me))?;
    fields[k + 1..].iter().all(atom).then_some(k)
}

/// The tail positions of `e`: through `let` bodies and `match` arms.
fn scan(e: &E, me: u32, s: &mut Scan) {
    match e {
        E::Let(r, a, b) => match op_path(*r, a, b, me) {
            Some(p) => s.acc.push(p),
            None => scan(b, me, s),
        },
        E::At(_, b) => scan(b, me, s),
        E::Case { arms, lits, default, .. } => {
            arms.iter().for_each(|a| scan(&a.body, me, s));
            lits.iter().for_each(|(_, b)| scan(b, me, s));
            if let Some(d) = default {
                scan(d, me, s);
            }
        }
        _ if con_path(e, me).is_some() => s.cons += 1,
        // Tail calls of `me` stay tail calls; anything else is a value.
        _ => {}
    }
}

/// How `f.acc` accumulates.
#[derive(Clone, Copy)]
enum Mode {
    /// `acc ⊕ f xs`, for a commutative `⊕`.
    Op(BOp),
    /// `f xs ++` what the accumulator holds, starting from the empty list.
    Pieces { nil: u32 },
}

fn acc_mode(paths: &[(BOp, bool)], nil: Option<u32>) -> Option<Mode> {
    let (op, _) = paths[0];
    let BOp::Prim(p, _) = op else { return None };
    if !paths.iter().all(|(o, _)| matches!(o, BOp::Prim(q, _) if *q == p)) {
        return None;
    }
    match p {
        // Commutative: `acc + f xs` whichever side the call is on.
        Op::Add | Op::Mul => Some(Mode::Op(op)),
        // `f xs ++ s` only.
        Op::Concat if paths.iter().all(|(_, call_left)| *call_left) => nil.map(|nil| Mode::Pieces { nil }),
        _ => None,
    }
}

/// Fresh variables for a function being rewritten.
struct Fresh(u32);

impl Fresh {
    fn var(&mut self) -> V {
        self.0 += 1;
        self.0 - 1
    }
}

/// `e` where it is no longer in tail position.
fn untail(e: E) -> E {
    match e {
        E::Call { f, args, .. } => E::Call { f, args, tail: false },
        E::Apply { f, args, .. } => E::Apply { f, args, tail: false },
        e => e,
    }
}

/// Rewrite the tail positions of `e` with `leaf`, which gets each one that
/// isn't a `let` or a `match`.
fn map_tail(e: E, leaf: &mut dyn FnMut(E) -> E) -> E {
    match e {
        E::Let(x, a, b) => E::Let(x, a, Box::new(map_tail(*b, leaf))),
        E::At(o, b) => E::At(o, Box::new(map_tail(*b, leaf))),
        E::Case { scrut, arms, lits, default } => E::Case {
            scrut,
            arms: arms.into_iter().map(|a| Arm { body: map_tail(a.body, leaf), ..a }).collect(),
            lits: lits.into_iter().map(|(l, b)| (l, map_tail(b, leaf))).collect(),
            default: default.map(|d| Box::new(map_tail(*d, leaf))),
        },
        e => leaf(e),
    }
}

fn new_helper(funcs: &mut Vec<Func>, i: usize, suffix: &str, extra: &[V], body: E, nvars: u32) {
    let f = &funcs[i];
    let mut params = f.params.clone();
    params.extend_from_slice(extra);
    let name = format!("{}.{suffix}", f.name);
    let owner = f.owner;
    // Its calls pass what calls of the function would.
    let bounds = f.bounds.clone();
    funcs.push(Func { name, owner, kind: FnKind::Global, params, body, nvars, rets: 1, bounds });
}

// ── an operator after the call ──────────────────────────────────────────────

fn acc(funcs: &mut Vec<Func>, i: usize, helper: u32, mode: Mode) {
    let me = i as u32;
    let body = funcs[i].body.clone();
    let mut fresh = Fresh(funcs[i].nvars);
    let acc = fresh.var();
    // `x` added to the accumulator: `acc ⊕ x`, or the piece `x` in front.
    let add = |x: E| match mode {
        Mode::Op(op) => E::Borrow { op, args: vec![E::Var(acc), x], drops: Vec::new() },
        Mode::Pieces { .. } => E::Borrow { op: BOp::ConcatPush, args: vec![x, E::Var(acc)], drops: Vec::new() },
    };
    // `f.acc xs acc`: each value `v` becomes `acc ⊕ v`, or `v ++` what `acc` holds.
    let finish = |v: E| match mode {
        Mode::Op(op) => E::Borrow { op, args: vec![E::Var(acc), v], drops: Vec::new() },
        Mode::Pieces { .. } => E::Borrow { op: BOp::ConcatAll, args: vec![v, E::Var(acc)], drops: Vec::new() },
    };
    let helper_body = map_acc(body, me, &mut |e, fresh: &mut Fresh| match e {
        // `x ⊕ f args` (or `f args ++ x`): `f.acc args (acc ⊕ x)` (or with
        // `x` in front of `acc`), the arguments first.
        Site::Op(args, x) => {
            let mut binds = Vec::new();
            let mut vs = Vec::new();
            for a in args {
                let v = fresh.var();
                binds.push((v, a));
                vs.push(E::Var(v));
            }
            let t = fresh.var();
            vs.push(E::Var(t));
            let call = E::Call { f: helper, args: vs, tail: true };
            let next = E::Let(t, Box::new(add(x)), Box::new(call));
            binds.into_iter().rev().fold(next, |b, (v, a)| E::Let(v, Box::new(a), Box::new(b)))
        }
        // `f args`: `f.acc args acc`.
        Site::Call(mut args) => {
            args.push(E::Var(acc));
            E::Call { f: helper, args, tail: true }
        }
        Site::Value(e @ E::Fail(_)) => e,
        // `acc * 1`, `acc + 0`: `acc`.
        Site::Value(e) if identity(mode, &e) => E::Var(acc),
        Site::Value(e) => {
            let r = fresh.var();
            E::Let(r, Box::new(untail(e)), Box::new(finish(E::Var(r))))
        }
    }, &mut fresh);
    new_helper(funcs, i, "acc", &[acc], helper_body, fresh.0);
    // `f` itself: `x ⊕ f args` is `f.acc args x`; `f args ++ x` is `f.acc`
    // with `x` in front of an empty accumulator.
    let body = std::mem::replace(&mut funcs[i].body, E::Erased);
    let mut fresh = Fresh(funcs[i].nvars);
    funcs[i].body = map_acc(body, me, &mut |e, fresh: &mut Fresh| match e {
        Site::Op(mut args, x) => match mode {
            Mode::Op(_) => {
                args.push(x);
                E::Call { f: helper, args, tail: true }
            }
            Mode::Pieces { nil } => {
                let (empty, ps) = (fresh.var(), fresh.var());
                args.push(E::Var(ps));
                let call = E::Call { f: helper, args, tail: true };
                let one = E::Borrow { op: BOp::ConcatPush, args: vec![x, E::Var(empty)], drops: Vec::new() };
                E::Let(empty, Box::new(E::Con { con: nil, fields: Vec::new(), reuse: None }), Box::new(E::Let(ps, Box::new(one), Box::new(call))))
            }
        },
        Site::Call(args) => E::Call { f: me, args, tail: true },
        Site::Value(e) => e,
    }, &mut fresh);
    funcs[i].nvars = fresh.0;
}

/// Is `e` the identity of `mode`'s operator, so that `acc ⊕ e` is `acc`?
/// (For `++`, `e` comes first: it is the result's start.)
fn identity(mode: Mode, e: &E) -> bool {
    matches!((mode, e), (Mode::Op(BOp::Prim(Op::Add, _)), E::Int(0)) | (Mode::Op(BOp::Prim(Op::Mul, _)), E::Int(1)))
}

/// A tail position, for the operator rewrite.
enum Site {
    /// `x ⊕ f args` or `f args ⊕ x`: the arguments and `x`.
    Op(Vec<E>, E),
    /// `f args`.
    Call(Vec<E>),
    /// Anything else.
    Value(E),
}

fn map_acc(e: E, me: u32, leaf: &mut dyn FnMut(Site, &mut Fresh) -> E, fresh: &mut Fresh) -> E {
    match e {
        E::Let(r, a, b) => {
            if op_path(r, &a, &b, me).is_some() {
                let (E::Call { args, .. }, E::Borrow { args: ops, .. }) = (*a, *b) else { unreachable!() };
                let x = ops.into_iter().find(|o| !matches!(o, E::Var(v) if *v == r)).expect("the other operand");
                return leaf(Site::Op(args, x), fresh);
            }
            E::Let(r, a, Box::new(map_acc(*b, me, leaf, fresh)))
        }
        E::At(o, b) => E::At(o, Box::new(map_acc(*b, me, leaf, fresh))),
        E::Case { scrut, arms, lits, default } => E::Case {
            scrut,
            arms: arms.into_iter().map(|a| Arm { body: map_acc(a.body, me, leaf, fresh), ..a }).collect(),
            lits: lits.into_iter().map(|(l, b)| (l, map_acc(b, me, leaf, fresh))).collect(),
            default: default.map(|d| Box::new(map_acc(*d, me, leaf, fresh))),
        },
        E::Call { f, args, .. } if f == me => leaf(Site::Call(args), fresh),
        e => leaf(Site::Value(e), fresh),
    }
}

// ── a constructor around the call ───────────────────────────────────────────

fn dps(funcs: &mut Vec<Func>, i: usize, helper: u32) {
    let me = i as u32;
    let body = funcs[i].body.clone();
    let mut fresh = Fresh(funcs[i].nvars);
    let dest = fresh.var();
    let idx = fresh.var();
    let set = |x: E| E::Borrow { op: BOp::SetField, args: vec![E::Var(dest), E::Var(idx), x], drops: Vec::new() };
    // `f.dps xs dest idx`: store `f xs` in field `idx` of `dest`.
    let helper_body = {
        let mut leaf = |e: E| -> E {
            if let Some(k) = con_path(&e, me) {
                // A new cell with the field empty, stored; then fill that field.
                let (con, args, hole) = open(e, k);
                let c = fresh.var();
                let u = fresh.var();
                let mut args = args;
                args.extend([E::Var(c), E::Int(k as i64)]);
                let call = E::Call { f: helper, args, tail: true };
                return E::Let(c, Box::new(E::Con { con, fields: hole, reuse: None }), Box::new(E::Let(u, Box::new(set(E::Var(c))), Box::new(call))));
            }
            match e {
                E::Call { f, mut args, .. } if f == me => {
                    args.extend([E::Var(dest), E::Var(idx)]);
                    E::Call { f: helper, args, tail: true }
                }
                e @ E::Fail(_) => e,
                e => {
                    let r = fresh.var();
                    E::Let(r, Box::new(untail(e)), Box::new(set(E::Var(r))))
                }
            }
        };
        map_tail(body, &mut leaf)
    };
    new_helper(funcs, i, "dps", &[dest, idx], helper_body, fresh.0);
    // `f` itself: build the cell, have `f.dps` fill it, return it.
    let body = std::mem::replace(&mut funcs[i].body, E::Erased);
    let mut fresh = Fresh(funcs[i].nvars);
    funcs[i].body = map_tail(body, &mut |e| {
        let Some(k) = con_path(&e, me) else { return e };
        let (con, mut args, hole) = open(e, k);
        let c = fresh.var();
        let u = fresh.var();
        args.extend([E::Var(c), E::Int(k as i64)]);
        let fill = E::Call { f: helper, args, tail: false };
        E::Let(c, Box::new(E::Con { con, fields: hole, reuse: None }), Box::new(E::Let(u, Box::new(fill), Box::new(E::Var(c)))))
    });
    funcs[i].nvars = fresh.0;
}

/// A constructor path: the constructor, the call's arguments, and the
/// fields with field `k` empty.
fn open(e: E, k: usize) -> (u32, Vec<E>, Vec<E>) {
    let E::Con { con, mut fields, .. } = e else { unreachable!() };
    let E::Call { args, .. } = std::mem::replace(&mut fields[k], E::Erased) else { unreachable!() };
    (con, args, fields)
}
