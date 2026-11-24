//! Builtins of the clock (`std.time`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.time.monotonic", "ckb_time_monotonic", ckb_time_monotonic),
    ("std.time.sleep_ns", "ckb_time_sleep_ns", ckb_time_sleep_ns),
];

builtin!(ckb_time_monotonic, |_a| of_num(crate::num::Num::S(crate::poll::now() as i128)));

// A duration no `u64` holds (585 years) sleeps as long as one can.
builtin!(ckb_time_sleep_ns, |a| {
    let ns = u64::try_from(num_of(a[1]).big()).unwrap_or(u64::MAX);
    crate::poll::sleep(ns);
    UNIT
});
