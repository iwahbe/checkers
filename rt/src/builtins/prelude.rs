//! Builtins of the prelude (`std.prelude`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.prelude.string_le", "ckb_string_le", ckb_string_le),
    ("std.prelude.valid_utf8", "ckb_valid_utf8", ckb_valid_utf8),
    ("std.prelude.array_rest", "ckb_array_rest", ckb_array_rest),
    ("std.prelude.string_first", "ckb_string_first", ckb_string_first),
    ("std.prelude.string_rest", "ckb_string_rest", ckb_string_rest),
];

// Whether bytes are UTF-8: what every string is (#170).
builtin!(ckb_valid_utf8, |a| bool_w(std::str::from_utf8(b(a[0])).is_ok()));

// Strings are ordered by their bytes, which for UTF-8 is the order of their
// characters' scalar values (D138).
builtin!(ckb_string_le, |a| bool_w(s(a[0]).as_bytes() <= s(a[1]).as_bytes()));

// All but the first element of a non-empty array: a slice sharing its
// storage (`Seq`'s instance for arrays, #169); an unshared slice moved
// forward in place (`OWNING`).
builtin!(ckb_array_rest, |a| crate::array::advance(a[0], 1));

// A non-empty string's first character, decoded (`Seq`'s instance for
// strings, #169).
builtin!(ckb_string_first, |a| match s(a[0]).chars().next() {
    Some(c) => nat(c as usize),
    None => bug("string_first of the empty string"),
});

// All but a non-empty string's first character: a slice sharing its bytes
// (`Seq`'s instance for strings, #169); an unshared slice moved forward in
// place (`OWNING`).
builtin!(ckb_string_rest, |a| {
    let w = s_obj(a[0]);
    match s(w).chars().next() {
        Some(c) if c.len_utf8() < blob(w).len() => crate::array::advance(w, c.len_utf8()),
        Some(c) => crate::array::slice(w, c.len_utf8(), blob(w).len()),
        None => bug("string_rest of the empty string"),
    }
});
