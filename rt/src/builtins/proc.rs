//! Builtins of child processes (`std.proc`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.proc.exec", "ckb_proc_exec", ckb_proc_exec),
];

builtin!(ckb_proc_exec, |a| {
    let args: Vec<&str> = list_items(a[1]).into_iter().map(s).collect();
    // Output written so far comes first.
    crate::io::flush();
    match std::process::Command::new(s(a[0])).args(args).status() {
        Ok(st) => {
            #[cfg(unix)]
            let signal = std::os::unix::process::ExitStatusExt::signal(&st);
            #[cfg(not(unix))]
            let signal: Option<i32> = None;
            let code = match (st.code(), signal) {
                (Some(c), _) => c as usize,
                (None, Some(sig)) => 128 + sig as usize,
                (None, None) => 1,
            };
            ok(nat(code))
        }
        Err(e) => err(describe_io(&e)),
    }
});
