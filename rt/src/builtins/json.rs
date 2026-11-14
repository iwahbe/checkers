//! Builtins of JSON (`std.json`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[("std.json.scan_number", "ckb_json_scan_number", ckb_json_scan_number)];

builtin!(ckb_json_scan_number, |a| match Decimal::scan_json(b(a[0]), n(a[1])) {
    Some((d, stop)) => some(parsed(new_obj(Obj::Decimal(d)), stop)),
    None => none(),
});
