//! Builtins of byte strings (`std.bytes`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.bytes.matches_at", "ckb_matches_at", ckb_matches_at),
    ("std.bytes.slice", "ckb_bytes_slice", ckb_bytes_slice),
    ("std.bytes.concat", "ckb_bytes_concat", ckb_bytes_concat),
];

builtin!(ckb_matches_at, |a| {
    let (src, i, word) = (b(a[0]), n(a[1]), b(a[2]));
    bool_w(i.checked_add(word.len()).is_some_and(|end| end <= src.len() && &src[i..end] == word))
});

builtin!(ckb_bytes_slice, |a| {
    let (src, i, j) = (b(a[0]), n(a[1]), n(a[2]));
    match src.get(i..j) {
        Some(x) => new_bytes(x),
        None => bug("`bytes.slice` out of range"),
    }
});

builtin!(ckb_bytes_concat, |a| {
    let parts = list_items(a[0]);
    let mut out = Vec::with_capacity(parts.iter().map(|p| b(*p).len()).sum());
    for p in parts {
        out.extend_from_slice(b(p));
    }
    new_bytes(&out)
});
