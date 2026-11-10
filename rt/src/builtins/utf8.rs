//! Builtins of UTF-8 (`std.utf8`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.utf8.encode", "ckb_string_bytes", super::string::ckb_string_bytes),
    ("std.utf8.decode_at", "ckb_decode_at", ckb_decode_at),
];

builtin!(ckb_decode_at, |a| {
    let (src, k) = (b(a[0]), n(a[1]));
    let rest = &src[k.min(src.len())..];
    let len = match rest.first() {
        Some(x) if *x < 0x80 => 1,
        Some(x) if *x >> 5 == 0b110 => 2,
        Some(x) if *x >> 4 == 0b1110 => 3,
        Some(x) if *x >> 3 == 0b11110 => 4,
        _ => 0,
    };
    match rest.get(..len).and_then(|x| std::str::from_utf8(x).ok()).and_then(|x| x.chars().next()) {
        Some(c) if len > 0 => some(parsed(nat(c as usize), k + len)),
        _ => none(),
    }
});
