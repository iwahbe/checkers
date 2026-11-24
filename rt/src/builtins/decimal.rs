//! Builtins of exact decimals (`std.decimal`).

#[allow(unused_imports)]
use super::*;
use crate::num::Num;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.decimal.of_int", "ckb_decimal_of_int", ckb_decimal_of_int),
    ("std.decimal.fixed", "ckb_decimal_fixed", ckb_decimal_fixed),
    ("std.decimal.scaled", "ckb_decimal_scaled", ckb_decimal_scaled),
    ("std.decimal.mantissa", "ckb_decimal_mantissa", ckb_decimal_mantissa),
    ("std.decimal.exponent", "ckb_decimal_exponent", ckb_decimal_exponent),
];

builtin!(ckb_decimal_fixed, |a| match obj(a[0]) {
    Some(Obj::Decimal(d)) => new_str(&d.fixed(num_of(a[1]).to_usize().unwrap_or(usize::MAX))),
    _ => bug("expected a Decimal"),
});

builtin!(ckb_decimal_of_int, |a| new_obj(Obj::Decimal(Decimal::new(num_of(a[0]).big(), 0.into()))));

builtin!(ckb_decimal_scaled, |a| new_obj(Obj::Decimal(Decimal::new(num_of(a[0]).big(), num_of(a[1]).big()))));

builtin!(ckb_decimal_mantissa, |a| match obj(a[0]) {
    Some(Obj::Decimal(d)) => of_num(Num::from_big(d.m.clone())),
    _ => bug("expected a Decimal"),
});

builtin!(ckb_decimal_exponent, |a| match obj(a[0]) {
    Some(Obj::Decimal(d)) => of_num(Num::from_big(d.e.clone())),
    _ => bug("expected a Decimal"),
});
