//! Builtins of concurrently owned cells (`std.cown`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.cown.new", "ckb_cown_new", ckb_cown_new),
];

builtin!(ckb_cown_new, |a| new_obj(Obj::Cown(new_cell(dup(a[0])))));
