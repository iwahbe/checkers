//! Builtins of the prelude (`std.prelude`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[("std.prelude.string_le", "ckb_string_le", ckb_string_le)];

// Strings are ordered by their bytes, which for UTF-8 is the order of their
// characters' scalar values (D138).
builtin!(ckb_string_le, |a| bool_w(s(a[0]).as_bytes() <= s(a[1]).as_bytes()));
