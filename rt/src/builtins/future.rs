//! Builtins of futures (`std.future`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.future.ready", "ckb_future_ready", ckb_future_ready),
];

builtin!(ckb_future_ready, |a| new_obj(Obj::Future(new_cell(dup(a[0])))));
