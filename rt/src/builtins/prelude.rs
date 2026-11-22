//! Builtins of the prelude (`std.prelude`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.prelude.string_le", "ckb_string_le", ckb_string_le),
    ("std.prelude.valid_utf8", "ckb_valid_utf8", ckb_valid_utf8),
];

// Whether bytes are UTF-8: what every string is (#170).
builtin!(ckb_valid_utf8, |a| bool_w(std::str::from_utf8(b(a[0])).is_ok()));

// Strings are ordered by their bytes, which for UTF-8 is the order of their
// characters' scalar values (D138).
builtin!(ckb_string_le, |a| bool_w(s(a[0]).as_bytes() <= s(a[1]).as_bytes()));
