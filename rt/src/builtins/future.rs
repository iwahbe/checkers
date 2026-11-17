//! Builtins of futures (`std.future`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.future.ready", "ckb_future_ready", ckb_future_ready),
    ("std.future.fork", "ckb_future_fork", ckb_future_fork),
    ("std.future.join", "ckb_future_join", ckb_future_join),
];

builtin!(ckb_future_ready, |a| new_obj(Obj::Future(new_cell(dup(a[0])))));

// `fork sched f` (D171): scheduled as a behaviour; `join x` (D176): the
// values, parking until they are there (`behav.rs`).
builtin!(ckb_future_fork, |a| crate::behav::ck_fork(a[1]));
builtin!(ckb_future_join, |a| crate::behav::join_values(a[0]));
