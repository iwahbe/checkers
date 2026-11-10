//! Builtins of characters (`std.char`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.char.code", "ckb_identity", ckb_identity),
    ("std.char.from_scalar", "ckb_identity", ckb_identity),
    ("std.char.from_ascii", "ckb_identity", ckb_identity),
    ("std.char.from_surrogates", "ckb_from_surrogates", ckb_from_surrogates),
];

builtin!(ckb_identity, |a| dup(a[0]));

builtin!(ckb_from_surrogates, |a| nat(0x10000 + ((n(a[0]) - 0xD800) << 10) + (n(a[1]) - 0xDC00)));
