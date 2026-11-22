//! Builtins of multisets (`std.bag`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.bag.of", "ckb_bag_of", ckb_bag_of),
    ("std.bag.count", "ckb_bag_count", ckb_bag_count),
    ("std.bag.sum", "ckb_bag_sum", ckb_bag_sum),
];

/// Entries by their text, sorted.
type Entries = std::collections::BTreeMap<String, crate::obj::BagEntry>;

fn add(m: &mut Entries, key: String, value: W, count: usize) {
    match m.get_mut(&key) {
        Some(e) => e.count += count,
        None => {
            m.insert(key.clone(), crate::obj::BagEntry { key, value: dup(value), count });
        }
    }
}

builtin!(ckb_bag_of, |a| {
    let mut m = Entries::new();
    for v in list_items(a[0]) {
        add(&mut m, crate::ops::show_derived(v, 0), v, 1);
    }
    new_obj(Obj::Bag(m.into_values().collect()))
});

builtin!(ckb_bag_count, |a| {
    let x = crate::ops::show_derived(a[0], 0);
    match obj(a[1]) {
        Some(Obj::Bag(bag)) => nat(bag.iter().find(|e| e.key == x).map_or(0, |e| e.count)),
        _ => bug("`bag.count` needs a bag"),
    }
});

builtin!(ckb_bag_sum, |a| match (obj(a[0]), obj(a[1])) {
    (Some(Obj::Bag(x)), Some(Obj::Bag(y))) => {
        let mut m = Entries::new();
        for e in x.iter().chain(y.iter()) {
            add(&mut m, e.key.clone(), e.value, e.count);
        }
        new_obj(Obj::Bag(m.into_values().collect()))
    }
    _ => bug("`bag.sum` needs bags"),
});
