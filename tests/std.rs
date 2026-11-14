//! The standard library is read from disk (D104): `CHECKERS_STD` picks the
//! directory, an edit to it takes effect without rebuilding `ckc`, and a
//! broken or missing standard library is reported, not hidden.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn ckc(std_dir: &Path, cwd: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ckc"))
        .args(args)
        .current_dir(cwd)
        .env("CHECKERS_STD", std_dir)
        .env("CHECKERS_NO_CACHE", "1")
        .output()
        .expect("run ckc")
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

/// A copy of the standard library, and a directory for a program.
fn scratch(name: &str) -> (PathBuf, PathBuf) {
    let dir = std::env::temp_dir().join(format!("checkers-std-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let (std_dir, prog) = (dir.join("std"), dir.join("prog"));
    std::fs::create_dir_all(&std_dir).unwrap();
    std::fs::create_dir_all(&prog).unwrap();
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("stdlib");
    for e in std::fs::read_dir(src).unwrap() {
        let e = e.unwrap();
        // Not `.checkers/`, the cache a check of a file here leaves (D100).
        if e.path().is_file() {
            std::fs::copy(e.path(), std_dir.join(e.file_name())).unwrap();
        }
    }
    (std_dir, prog)
}

fn append(path: &Path, more: &str) {
    let mut s = std::fs::read_to_string(path).unwrap();
    s += more;
    std::fs::write(path, s).unwrap();
}

#[test]
fn edits_take_effect_without_rebuilding() {
    let (std_dir, prog) = scratch("edit");
    append(&std_dir.join("list.ck"), "\nexport fn second xs -> n : xs~List Nat, n~Nat\n    match xs\n        _ :: y :: _ -> y\n        _           -> 0\n");
    std::fs::write(prog.join("p.ck"), "module p\n\nimport std.list\n\ncheck list.second [1, 2, 3] == 2\n").unwrap();
    let out = ckc(&std_dir, &prog, &["check", "p.ck"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert_eq!(text(&out.stderr), "p.ck: 0 errors, 0 warnings\n");
}

#[test]
fn missing_standard_library() {
    let (_, prog) = scratch("missing");
    let nowhere = prog.join("nowhere");
    std::fs::write(prog.join("p.ck"), "module p\n").unwrap();
    let out = ckc(&nowhere, &prog, &["check", "p.ck"]);
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(
        text(&out.stderr),
        format!(
            "error: the standard library was not found; looked in:\n  {}\nhelp: set CHECKERS_STD to the directory holding prelude.ck\n",
            nowhere.display()
        )
    );
}

#[test]
fn misnamed_standard_library_module() {
    let (std_dir, prog) = scratch("misnamed");
    let bag = std_dir.join("bag.ck");
    let s = std::fs::read_to_string(&bag).unwrap().replace("module std.bag", "module bag");
    std::fs::write(&bag, s).unwrap();
    std::fs::write(prog.join("p.ck"), "module p\n\nimport std.bag\n").unwrap();
    let out = ckc(&std_dir, &prog, &["check", "p.ck"]);
    assert_eq!(out.status.code(), Some(1));
    let err = text(&out.stderr);
    assert!(err.contains("error[E0223]: this file must declare `module std.bag`, because it is imported as `std.bag`"), "{err}");
    assert!(err.contains(" --> <std>/bag.ck:"), "{err}");
}

#[test]
fn builtin_without_implementation() {
    let (std_dir, prog) = scratch("builtin");
    append(&std_dir.join("bag.ck"), "\nexport fn twice b -> c : b~Bag, c~Bag\n    __builtin\n");
    std::fs::write(prog.join("p.ck"), "module p\n\nimport std.bag\n").unwrap();
    let out = ckc(&std_dir, &prog, &["check", "p.ck"]);
    assert_eq!(out.status.code(), Some(1));
    let err = text(&out.stderr);
    assert!(err.contains("error[E0361]: the runtime has no builtin `std.bag.twice`"), "{err}");
    assert!(err.contains("help: add it to `rt/src/builtins/bag.rs`, or give `twice` a body in Checkers"), "{err}");
}

/// Every builtin the runtime implements is listed in SPEC §16.3, in its
/// module's row (M13).
#[test]
fn every_builtin_is_in_the_spec() {
    let spec = std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("SPEC.md")).unwrap();
    let start = spec.find("### 16.3").expect("§16.3");
    let table = &spec[start..start + spec[start..].find("\n### ").unwrap()];
    let mut missing = Vec::new();
    for (name, _, _) in checkers_rt::builtins::all() {
        let (module, f) = name.rsplit_once('.').unwrap();
        let row = table.lines().find(|l| l.starts_with('|') && l.split('|').nth(1).is_some_and(|c| c.contains(&format!("`{module}`"))));
        if !row.is_some_and(|r| r.split('|').nth(3).is_some_and(|c| c.contains(&format!("`{f}`")))) {
            missing.push(*name);
        }
    }
    assert!(missing.is_empty(), "builtins missing from SPEC §16.3: {missing:?}");
}

/// A standard-library file checked by itself (as an editor does) is checked
/// as the standard library: `__builtin` is allowed (D145).
#[test]
fn checking_a_standard_library_file() {
    let (std_dir, prog) = scratch("itself");
    for m in ["decimal.ck", "prelude.ck", "json.ck"] {
        let out = ckc(&std_dir, &prog, &["check", std_dir.join(m).to_str().unwrap()]);
        let err = text(&out.stderr);
        assert!(out.status.success(), "{m}:\n{err}");
        assert!(err.ends_with(&format!("{m}: 0 errors, 0 warnings\n")), "{m}:\n{err}");
    }
    // A file elsewhere that says it is a standard-library module is not.
    std::fs::write(prog.join("fake.ck"), "module std.fake\n\nexport fn f n -> m : n~Int, m~Int\n    __builtin\n").unwrap();
    let out = ckc(&std_dir, &prog, &["check", "fake.ck"]);
    assert!(text(&out.stderr).contains("E0356"), "{}", text(&out.stderr));
}

/// Its proofs and `check`s run once (D145).
#[test]
fn a_standard_library_file_reports_once() {
    let (std_dir, prog) = scratch("once");
    append(&std_dir.join("sort.ck"), "\ncheck sort [2, 1] == [2, 1]\n\nfn bigger n -> m : n~Nat, m~Nat, m > n\n    n\n");
    let out = ckc(&std_dir, &prog, &["check", std_dir.join("sort.ck").to_str().unwrap()]);
    let err = text(&out.stderr);
    assert_eq!(err.matches("error[E0260]").count(), 1, "{err}");
    assert_eq!(err.matches("error[E0450]").count(), 1, "{err}");
}
