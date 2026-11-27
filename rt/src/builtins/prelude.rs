//! Builtins of the prelude (`std.prelude`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.prelude.string_le", "ckb_string_le", ckb_string_le),
    ("std.prelude.valid_utf8", "ckb_valid_utf8", ckb_valid_utf8),
    ("std.prelude.array_rest", "ckb_array_rest", ckb_array_rest),
    ("std.prelude.array_mismatch", "ckb_array_mismatch", ckb_array_mismatch),
    ("std.prelude.string_first", "ckb_string_first", ckb_string_first),
    ("std.prelude.string_rest", "ckb_string_rest", ckb_string_rest),
];

// Whether bytes are UTF-8: what every string is (#170).
builtin!(ckb_valid_utf8, |a| bool_w(std::str::from_utf8(b(a[0])).is_ok()));

// Strings are ordered by their bytes, which for UTF-8 is the order of their
// characters' scalar values (#625).
builtin!(ckb_string_le, |a| bool_w(s(a[0]).as_bytes() <= s(a[1]).as_bytes()));

// All but the first element of a non-empty array: a slice sharing its
// storage (`Seq`'s instance for arrays, #169); an unshared slice moved
// forward in place (`OWNING`).
builtin!(ckb_array_rest, |a| crate::array::advance(a[0], 1));

// The first index where two arrays differ, or the shorter one's length:
// where `Ord (Array a)` compares them. Arrays stored alike in bytes are
// compared a block of bytes at a time; others element by element, by `==`.
builtin!(ckb_array_mismatch, |a| {
    use crate::array::{data, get, layout, len, Layout};
    let (x, y) = (a[0], a[1]);
    let n = len(x).min(len(y));
    let l = layout(x);
    if l == layout(y) && l != Layout::Words {
        let w = l.width();
        let (p, q) = unsafe { (std::slice::from_raw_parts(data(x), n * w), std::slice::from_raw_parts(data(y), n * w)) };
        return nat(first_difference(p, q) / w);
    }
    if l == Layout::Words && layout(y) == Layout::Words {
        // One word is one value (a number, or the same object); different
        // words are compared structurally.
        let (p, q) = unsafe { (std::slice::from_raw_parts(data(x) as *const W, n), std::slice::from_raw_parts(data(y) as *const W, n)) };
        let same = |i: usize| p[i] == q[i] || crate::ops::equal(p[i], q[i]).unwrap_or_else(|what| bug(what));
        return nat((0..n).find(|&i| !same(i)).unwrap_or(n));
    }
    let differs = |i| {
        let (s, t) = (get(x, i), get(y, i));
        let same = crate::ops::equal(s, t);
        drop_w(s);
        drop_w(t);
        !same.unwrap_or_else(|what| bug(what))
    };
    nat((0..n).find(|&i| differs(i)).unwrap_or(n))
});

/// The first index where `p` and `q` (of one length) differ, or their
/// length: equal blocks are skipped with `memcmp`.
fn first_difference(p: &[u8], q: &[u8]) -> usize {
    const BLOCK: usize = 64;
    let mut i = 0;
    while i + BLOCK <= p.len() && p[i..i + BLOCK] == q[i..i + BLOCK] {
        i += BLOCK;
    }
    i + p[i..].iter().zip(&q[i..]).position(|(s, t)| s != t).unwrap_or(p.len() - i)
}

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

#[cfg(test)]
mod tests {
    use super::first_difference;

    #[test]
    fn first_difference_in_and_after_blocks() {
        let p = vec![7u8; 200];
        assert_eq!(first_difference(&p, &p), 200);
        for i in [0, 63, 64, 130, 199] {
            let mut q = p.clone();
            q[i] = 8;
            assert_eq!(first_difference(&p, &q), i);
        }
        assert_eq!(first_difference(&[], &[]), 0);
    }
}
