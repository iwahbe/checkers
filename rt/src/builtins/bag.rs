//! Builtins of multisets of numbers (`std.bag`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.bag.of", "ckb_bag_of", ckb_bag_of),
    ("std.bag.count", "ckb_bag_count", ckb_bag_count),
    ("std.bag.sum", "ckb_bag_sum", ckb_bag_sum),
];

builtin!(ckb_bag_of, |a| {
    let mut counts: std::collections::BTreeMap<Num, usize> = std::collections::BTreeMap::new();
    for v in list_items(a[0]) {
        *counts.entry(num_of(v)).or_default() += 1;
    }
    new_obj(Obj::Bag(counts.into_iter().collect()))
});

builtin!(ckb_bag_count, |a| {
    let x = num_of(a[0]);
    match obj(a[1]) {
        Some(Obj::Bag(bag)) => nat(bag.iter().find(|(v, _)| *v == x).map_or(0, |(_, c)| *c)),
        _ => bug("`bag.count` needs a bag"),
    }
});

builtin!(ckb_bag_sum, |a| match (obj(a[0]), obj(a[1])) {
    (Some(Obj::Bag(x)), Some(Obj::Bag(y))) => {
        let mut counts: std::collections::BTreeMap<Num, usize> = x.iter().cloned().collect();
        for (v, c) in y.iter() {
            *counts.entry(v.clone()).or_default() += c;
        }
        new_obj(Obj::Bag(counts.into_iter().collect()))
    }
    _ => bug("`bag.sum` needs bags"),
});
