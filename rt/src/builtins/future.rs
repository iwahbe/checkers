//! Builtins of futures (`std.future`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.future.ready", "ckb_future_ready", ckb_future_ready),
    ("std.future.fork", "ckb_future_fork", ckb_future_fork),
    ("std.future.join", "ckb_future_join", ckb_future_join),
    ("std.future.both", "ckb_future_both", ckb_future_both),
];

builtin!(ckb_future_ready, |a| new_obj(Obj::Future(new_cell(dup(a[0])))));

// `fork sched f`, `join x sched f`, `both x y` (D171): behaviours, as the
// runtime's `ck_fork` and `ck_join` run them.
builtin!(ckb_future_fork, |a| crate::behav::ck_fork(a[1]));
builtin!(ckb_future_join, |a| crate::behav::ck_join(a[0], a[2]));
builtin!(ckb_future_both, |a| crate::behav::ck_both(a[0], a[1]));
