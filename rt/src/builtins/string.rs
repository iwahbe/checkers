//! Builtins of strings (`std.string`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.string.from_chars", "ckb_from_chars", ckb_from_chars),
    ("std.string.from_char", "ckb_from_char", ckb_from_char),
    ("std.string.concat_map", "ckb_concat_map", ckb_concat_map),
    ("std.string.bytes", "ckb_string_bytes", ckb_string_bytes),
    ("std.string.concat", "ckb_string_concat", ckb_string_concat),
    ("std.string.from_utf8", "ckb_from_utf8", ckb_from_utf8),
];

builtin!(ckb_from_chars, |a| {
    let st: String = list_items(a[0]).into_iter().map(ch).collect();
    new_str(&st)
});

builtin!(ckb_from_char, |a| new_str(&ch(a[0]).to_string()));

builtin!(ckb_concat_map, |a| {
    let mut out = String::new();
    for c in s(a[1]).chars() {
        let r = crate::apply::apply(dup(a[0]), vec![nat(c as usize)]);
        out.push_str(s(r));
        drop_w(r);
    }
    new_str(&out)
});

builtin!(ckb_string_bytes, |a| new_bytes(s(a[0]).as_bytes()));

builtin!(ckb_string_concat, |a| {
    let parts = list_items(a[0]);
    let mut out = String::with_capacity(parts.iter().map(|p| s(*p).len()).sum());
    for p in parts {
        out.push_str(s(p));
    }
    new_str(&out)
});

builtin!(ckb_from_utf8, |a| match std::str::from_utf8(b(a[0])) {
    Ok(t) => some(new_str(t)),
    Err(_) => none(),
});
