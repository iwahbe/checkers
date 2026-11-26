//! Standard input that can't be read (SPEC §13.4): `terminal.read_line`
//! gives the operating system's error, which a golden run case can't show,
//! its input being a pipe.

use std::process::{Command, Stdio};

#[test]
fn a_failed_read_of_standard_input_is_an_error() {
    // A directory opens for reading, but reading it fails.
    let dir = std::fs::File::open(env!("CARGO_MANIFEST_DIR")).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_ckc"))
        .args(["run", "tests/run/terminal_lines.ck"])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .env("CHECKERS_NO_CACHE", "1")
        .stdin(Stdio::from(dir))
        .output()
        .expect("run ckc");
    assert_eq!(String::from_utf8_lossy(&out.stdout), "read failed: Is a directory\n");
    assert_eq!(String::from_utf8_lossy(&out.stderr), "");
    assert!(out.status.success());
}
