//! Builtins of the process environment (`std.env`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.env.get", "ckb_env_get", ckb_env_get),
    ("std.env.executable", "ckb_env_executable", ckb_env_executable),
];

builtin!(ckb_env_get, |a| match std::env::var(s(a[0])) {
    Ok(v) => some(new_str(&v)),
    Err(_) => none(),
});

builtin!(ckb_env_executable, |_a| match std::env::current_exe() {
    Ok(p) => match p.to_str() {
        Some(t) => some(new_str(t)),
        None => none(),
    },
    Err(_) => none(),
});
