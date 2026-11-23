//! Builtins of exact decimals (`std.decimal`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.decimal.render", "ckb_decimal_render", ckb_decimal_render),
    ("std.decimal.of_int", "ckb_decimal_of_int", ckb_decimal_of_int),
    ("std.decimal.fixed", "ckb_decimal_fixed", ckb_decimal_fixed),
    ("std.decimal.scaled", "ckb_decimal_scaled", ckb_decimal_scaled),
];

builtin!(ckb_decimal_fixed, |a| match obj(a[0]) {
    Some(Obj::Decimal(d)) => new_str(&d.fixed(num_of(a[1]).to_usize().unwrap_or(usize::MAX))),
    _ => bug("expected a Decimal"),
});

builtin!(ckb_decimal_render, |a| match obj(a[0]) {
    Some(Obj::Decimal(d)) => new_str(&d.render()),
    _ => bug("expected a Decimal"),
});

builtin!(ckb_decimal_of_int, |a| new_obj(Obj::Decimal(Decimal::new(num_of(a[0]).big(), 0.into()))));

builtin!(ckb_decimal_scaled, |a| new_obj(Obj::Decimal(Decimal::new(num_of(a[0]).big(), num_of(a[1]).big()))));
