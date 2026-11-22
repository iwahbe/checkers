//! Builtins of the prelude (`std.prelude`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.prelude.string_le", "ckb_string_le", ckb_string_le),
    ("std.prelude.valid_utf8", "ckb_valid_utf8", ckb_valid_utf8),
    ("std.prelude.array_rest", "ckb_array_rest", ckb_array_rest),
    ("std.prelude.string_uncons", "ckb_string_uncons", ckb_string_uncons),
];

// Whether bytes are UTF-8: what every string is (#170).
builtin!(ckb_valid_utf8, |a| bool_w(std::str::from_utf8(b(a[0])).is_ok()));

// Strings are ordered by their bytes, which for UTF-8 is the order of their
// characters' scalar values (D138).
builtin!(ckb_string_le, |a| bool_w(s(a[0]).as_bytes() <= s(a[1]).as_bytes()));

// All but the first element of a non-empty array: a slice sharing its
// storage (`Seq`'s instance for arrays, #169).
builtin!(ckb_array_rest, |a| crate::array::slice(a[0], 1, crate::array::len(a[0])));

// A string's first character and the rest, a slice of its bytes; `None` for
// the empty string (`Seq`'s instance for strings, #169).
builtin!(ckb_string_uncons, |a| {
    let w = s_obj(a[0]);
    match s(w).chars().next() {
        Some(c) => {
            let k = c.len_utf8();
            some(new_tuple(&[nat(c as usize), crate::array::slice(w, k, blob(w).len())]))
        }
        None => none(),
    }
});
