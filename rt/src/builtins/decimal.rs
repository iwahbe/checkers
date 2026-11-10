//! Builtins of exact decimals (`std.decimal`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.decimal.scan_json", "ckb_scan_json", ckb_scan_json),
    ("std.decimal.render", "ckb_decimal_render", ckb_decimal_render),
    ("std.decimal.of_int", "ckb_decimal_of_int", ckb_decimal_of_int),
];

builtin!(ckb_scan_json, |a| match Decimal::scan_json(b(a[0]), n(a[1])) {
    Some((d, stop)) => some(parsed(new_obj(Obj::Decimal(d)), stop)),
    None => none(),
});

builtin!(ckb_decimal_render, |a| match obj(a[0]) {
    Some(Obj::Decimal(d)) => new_str(&d.render()),
    _ => bug("expected a Decimal"),
});

builtin!(ckb_decimal_of_int, |a| new_obj(Obj::Decimal(Decimal::new(num_of(a[0]).big(), 0))));
