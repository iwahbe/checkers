//! A value nested a million deep is shown as a short one is. A failed
//! `check` shows its sides in full, so its golden output would be megabytes:
//! this test looks at the start and end of the message instead.

use std::process::Command;

const SOURCE: &str = "module deep_values

enum Snoc
    Lin
    Snoc s n : s~Snoc, n~Nat

fn snoc_onto s n -> r : s~Snoc, n~Nat, r~Snoc
    decreasing n
    if n == 0 then s else snoc_onto (Snoc s 1) (n - 1)

check snoc_onto Lin 1000000 == Lin
";

#[test]
fn a_failed_check_shows_a_deep_value() {
    let dir = std::env::temp_dir().join(format!("checkers-deep-values-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("deep_values.ck"), SOURCE).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_ckc"))
        .args(["check", "--no-cache", "deep_values.ck"])
        .current_dir(&dir)
        .output()
        .expect("run ckc");
    let _ = std::fs::remove_dir_all(&dir);
    let report = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "{report}");
    assert!(report.contains("error[E0260]: this `check` is false"), "{report}");
    let left = report.lines().find_map(|l| l.trim_start().strip_prefix("= note: left side:  `")).expect("the left side");
    // `Snoc (Snoc Lin 1) 1`, a million deep.
    let shown = format!("{}Snoc Lin 1{}`", "Snoc (".repeat(999_999), ") 1".repeat(999_999));
    assert!(left == shown, "left side: {}…", &left[..left.len().min(80)]);
    assert!(report.contains("= note: right side: `Lin`"), "{report}");
    assert!(report.ends_with("deep_values.ck: 1 error, 0 warnings\n"), "{}", &report[report.len().saturating_sub(200)..]);
}
