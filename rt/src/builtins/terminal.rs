//! Builtins of standard input and output (`std.terminal`).

#[allow(unused_imports)]
use super::*;

/// Each builtin: its standard-library name, symbol and function.
pub const TABLE: &[Builtin] = &[
    ("std.terminal.print_line", "ckb_print_line", ckb_print_line),
    ("std.terminal.eprint_line", "ckb_eprint_line", ckb_eprint_line),
    ("std.terminal.read_all", "ckb_read_all", ckb_read_all),
    ("std.terminal.read_line", "ckb_read_line", ckb_read_line),
    ("std.terminal.write", "ckb_write", ckb_write),
    ("std.terminal.write_bytes", "ckb_write_bytes", ckb_write_bytes),
];

builtin!(ckb_print_line, |a| {
    crate::io::print_line(s(a[0]));
    UNIT
});

builtin!(ckb_eprint_line, |a| {
    crate::io::eprint_line(s(a[0]));
    UNIT
});

builtin!(ckb_read_all, |_a| match crate::io::read_all() {
    Ok(buf) => ok(new_bytes(&buf)),
    Err(e) => err(describe_io(&e)),
});

builtin!(ckb_read_line, |_a| match crate::io::read_line() {
    Some(l) => some(new_str(&l)),
    None => none(),
});

builtin!(ckb_write, |a| {
    crate::io::write(s(a[0]).as_bytes());
    UNIT
});

builtin!(ckb_write_bytes, |a| {
    crate::io::write(b(a[0]));
    UNIT
});
