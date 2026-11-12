//! Builtins of arrays (`std.array`, D133). Each gets its element type's
//! layout first (a type argument's word, `array::Layout::of_word`).

#[allow(unused_imports)]
use super::*;
use crate::array::{self, Layout};

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.array.from_list", "ckb_array_from_list", ckb_array_from_list),
    ("std.array.to_list", "ckb_array_to_list", ckb_array_to_list),
    ("std.array.repeat", "ckb_array_repeat", ckb_array_repeat),
    ("std.array.set", "ckb_array_set", ckb_array_set),
    ("std.array.slice", "ckb_array_slice", ckb_array_slice),
    ("std.array.concat", "ckb_array_concat", ckb_array_concat),
    ("std.array.reverse", "ckb_array_reverse", ckb_array_reverse),
];

builtin!(ckb_array_from_list, |a| {
    let items: Vec<W> = list_items(a[1]).into_iter().map(dup).collect();
    array::from_items(Layout::of_word(a[0]), items)
});

builtin!(ckb_array_to_list, |a| list(array::items(a[1])));

builtin!(ckb_array_repeat, |a| {
    let items: Vec<W> = (0..n(a[1])).map(|_| dup(a[2])).collect();
    array::from_items(Layout::of_word(a[0]), items)
});

builtin!(ckb_array_set, |a| array::set(a[1], n(a[2]), a[3]));

builtin!(ckb_array_slice, |a| array::slice(a[1], n(a[2]), n(a[3])));

builtin!(ckb_array_concat, |a| {
    let mut items = Vec::new();
    for part in list_items(a[1]) {
        items.extend(array::items(part));
    }
    array::from_items(Layout::of_word(a[0]), items)
});

builtin!(ckb_array_reverse, |a| array::reverse(a[1]));
