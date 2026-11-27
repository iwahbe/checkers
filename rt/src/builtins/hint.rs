//! Builtins of hints to the compiler (`std.hint`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[("std.hint.blackbox", "ckb_hint_blackbox", ckb_hint_blackbox)];

// The value it is given: the compiler never computes a call of it
// (SPEC §8.9), so the value reaches the program only when it runs.
builtin!(ckb_hint_blackbox, |a| dup(a[0]));
