//! Builtins of strings (`std.string`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.string.chars", "ckb_string_chars", ckb_string_chars),
    ("std.string.from_chars", "ckb_from_chars", ckb_from_chars),
    ("std.string.from_char", "ckb_from_char", ckb_from_char),
    ("std.string.bytes", "ckb_string_bytes", ckb_string_bytes),
    ("std.string.concat", "ckb_string_concat", ckb_string_concat),
    ("std.string.from_utf8", "ckb_from_utf8", ckb_from_utf8),
    ("std.string.debug", "ckb_debug", ckb_debug),
];

// `debug x` (#126): `x` as Checkers source.
builtin!(ckb_debug, |a| new_str(&crate::ops::show_typed(a[1], &crate::desc::Ty::of_word(a[0]), 0)));

builtin!(ckb_from_chars, |a| {
    let st: String = list_items(a[0]).into_iter().map(ch).collect();
    new_str(&st)
});

builtin!(ckb_from_char, |a| {
    if is_int(a[0]) {
        if let Some(s) = u32::try_from(int_of(a[0])).ok().and_then(ascii_str) {
            return s;
        }
    }
    new_str(ch(a[0]).encode_utf8(&mut [0; 4]))
});

// A string is stored as its bytes (#170): the same object.
builtin!(ckb_string_bytes, |a| dup(s_obj(a[0])));

builtin!(ckb_string_concat, |a| {
    let parts = list_items(a[0]);
    let mut out = String::with_capacity(parts.iter().map(|p| s(*p).len()).sum());
    for p in parts {
        out.push_str(s(p));
    }
    new_str(&out)
});

// Bytes that are UTF-8 are a string as they are (#170): the same object.
builtin!(ckb_from_utf8, |a| match std::str::from_utf8(b(a[0])) {
    Ok(_) => some(dup(a[0])),
    Err(_) => none(),
});

builtin!(ckb_string_chars, |a| list(s(a[0]).chars().map(|c| crate::obj::nat(c as usize)).collect()));
