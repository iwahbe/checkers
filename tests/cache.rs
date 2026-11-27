//! Z3's answers are cached (D100): a second check reuses them, an entry
//! whose query doesn't match exactly is ignored, and `--no-cache` neither
//! reads nor writes the cache. Verified modules are remembered (D143): a
//! module is not verified again while nothing it depends on has changed:
//! its text, its imports, and the modules of the instances it uses. The
//! counts are read from `CHECKERS_CACHE_STATS=1`'s lines on standard error.

use std::path::{Path, PathBuf};
use std::process::Command;

/// `ckc ARGS`, which must succeed: its standard output, then its standard
/// error (where the cache's counts are).
fn ckc(dir: &Path, args: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_ckc")).args(args).env("CHECKERS_CACHE_STATS", "1").current_dir(dir).output().expect("run ckc");
    assert!(out.status.success(), "ckc {args:?}: {}", String::from_utf8_lossy(&out.stderr));
    format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("checkers-cache-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    std::fs::copy(root.join("examples/sort.ck"), dir.join("sort.ck")).unwrap();
    dir
}

fn cache_line(out: &str) -> Option<String> {
    out.lines().find(|l| l.starts_with("cache: ") && !l.contains("modules")).map(str::to_string)
}

/// Forget the verified modules (D143), so the next check asks Z3 again.
fn forget_modules(dir: &Path) {
    let _ = std::fs::remove_dir_all(dir.join(".checkers/modules"));
}

/// Answers reused, out of answers asked for.
fn counts(out: &str) -> (usize, usize) {
    match cache_line(out) {
        None => (0, 0),
        Some(line) => {
            let nums: Vec<usize> = line.split_whitespace().filter_map(|w| w.parse().ok()).collect();
            assert_eq!(nums.len(), 2, "{line}");
            (nums[0], nums[1])
        }
    }
}

/// The output without its cache lines (the diagnostics and the count of
/// obligations proved): the same, cached or not.
fn proofs(out: &str) -> String {
    out.lines().filter(|l| !l.starts_with("cache: ")).map(|l| format!("{l}\n")).collect()
}

#[test]
fn second_check_reuses_answers() {
    let dir = scratch("reuse");
    let first = ckc(&dir, &["check", "sort.ck"]);
    // Only a query asked twice in one run (the same text, so the same answer)
    // can be reused, and only if the first answer is stored before the second
    // is asked: when both run at once, nothing is.
    let (reused, asked) = counts(&first);
    assert!(asked > 0 && reused * 2 < asked, "nothing cached yet:\n{first}");
    forget_modules(&dir);
    let second = ckc(&dir, &["check", "sort.ck"]);
    let (reused, asked) = counts(&second);
    assert!(asked > 0, "a cache line:\n{second}");
    assert_eq!(reused, asked, "every answer reused:\n{second}");
    assert_eq!(proofs(&first), proofs(&second));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn mismatched_entry_is_ignored() {
    let dir = scratch("mismatch");
    let first = ckc(&dir, &["check", "sort.ck"]);
    forget_modules(&dir);
    // Change one byte of each stored query: as a hash collision would look.
    for e in std::fs::read_dir(dir.join(".checkers/z3")).unwrap() {
        let p = e.unwrap().path();
        if p.is_dir() {
            continue;
        }
        let text = std::fs::read_to_string(&p).unwrap();
        let (header, rest) = text.split_once('\n').unwrap();
        let changed = rest.replacen("(set-logic ALL)", "(set-logic ALl)", 1);
        std::fs::write(&p, format!("{header}\n{changed}")).unwrap();
    }
    let again = ckc(&dir, &["check", "sort.ck"]);
    // No stored entry matches: as in a first run, at most a query asked twice
    // in this run is reused.
    let (reused, asked) = counts(&again);
    assert!(asked > 0 && reused * 2 < asked, "no entry matches:\n{again}");
    assert_eq!(proofs(&first), proofs(&again));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn no_cache_flag() {
    let dir = scratch("off");
    ckc(&dir, &["check", "--no-cache", "sort.ck"]);
    assert!(!dir.join(".checkers").exists());
    let _ = std::fs::remove_dir_all(&dir);
}

/// The number of modules remembered (D143), out of the program's modules.
fn modules(out: &str) -> Option<(usize, usize)> {
    let line = out.lines().find(|l| l.contains("modules verified before"))?;
    let nums: Vec<usize> = line.split_whitespace().filter_map(|w| w.parse().ok()).collect();
    Some((nums[0], nums[1]))
}

fn ckc_status(dir: &Path, args: &[&str]) -> (bool, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_ckc")).args(args).current_dir(dir).output().expect("run ckc");
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    (out.status.success(), text)
}

#[test]
fn verified_modules_are_remembered() {
    let dir = scratch("modules");
    let first = ckc(&dir, &["check", "sort.ck"]);
    assert!(modules(&first).is_some_and(|(k, _)| k == 0), "nothing remembered yet:\n{first}");
    let second = ckc(&dir, &["check", "sort.ck"]);
    let (k, n) = modules(&second).unwrap_or_else(|| panic!("a modules line:\n{second}"));
    assert!(n > 0 && k == n, "every module remembered:\n{second}");
    assert_eq!(proofs(&first), proofs(&second));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn edited_module_is_checked_again() {
    let dir = scratch("edited");
    ckc(&dir, &["check", "sort.ck"]);
    let text = std::fs::read_to_string(dir.join("sort.ck")).unwrap();
    let wrong = text.replace("check sort [3, 1, 2] == [1, 2, 3]", "check sort [3, 1, 2] == [3, 2, 1]");
    assert_ne!(text, wrong);
    std::fs::write(dir.join("sort.ck"), wrong).unwrap();
    let (ok, out) = ckc_status(&dir, &["check", "sort.ck"]);
    assert!(!ok, "the false check fails:\n{out}");
    // A failed check remembers nothing: it fails again.
    let (ok, again) = ckc_status(&dir, &["check", "sort.ck"]);
    assert!(!ok, "still fails:\n{again}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn editing_an_import_forgets_its_importer() {
    let dir = scratch("import");
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    std::fs::copy(root.join("examples/resort.ck"), dir.join("resort.ck")).unwrap();
    ckc(&dir, &["check", "resort.ck"]);
    let all = ckc(&dir, &["check", "resort.ck"]);
    let (k, n) = modules(&all).unwrap();
    assert_eq!(k, n, "{all}");
    // A comment changes `sort`'s text, so `sort` and `resort` are verified again.
    let text = std::fs::read_to_string(dir.join("sort.ck")).unwrap();
    std::fs::write(dir.join("sort.ck"), format!("{text}\n# edited\n")).unwrap();
    let after = ckc(&dir, &["check", "resort.ck"]);
    let (k2, n2) = modules(&after).unwrap();
    assert_eq!((k2, n2), (n - 2, n), "{after}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn remembered_module_keeps_its_warnings() {
    let dir = scratch("warnings");
    std::fs::write(
        dir.join("never.ck"),
        "module never\n\nfn sign n -> r : n~Nat, r~Int\n    if n < 0 then -1 else 1\n\ncheck sign 2 == 1\n",
    )
    .unwrap();
    let (_, first) = ckc_status(&dir, &["check", "never.ck"]);
    assert!(first.contains("W022"), "a branch that never runs:\n{first}");
    let (_, second) = ckc_status(&dir, &["check", "never.ck"]);
    assert!(second.contains("W022"), "still reported when the module is remembered (D143):\n{second}");
    let third = ckc(&dir, &["check", "never.ck"]);
    assert!(modules(&third).is_some_and(|(k, n)| k == n), "{third}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A module can use an instance declared in a module it doesn't import
/// (instances are found wherever their module is loaded, §9.8): editing that
/// instance forgets the module that used it.
#[test]
fn editing_an_unimported_instance_forgets_its_user() {
    let dir = scratch("instance");
    std::fs::create_dir_all(dir.join("k")).unwrap();
    std::fs::write(dir.join("k/cls.ck"), "module k.cls\n\nexport class Make t\n    fn make u -> r : u~Int, r~t\n").unwrap();
    let inst = |post: &str, body: &str| {
        format!("module k.inst\n\nimport k.cls (Make)\n\ninstance Make Int\n    fn make u -> r : u~Int, r~Int, r == {post}\n        {body}\n")
    };
    std::fs::write(dir.join("k/inst.ck"), inst("u + 1", "u + 1")).unwrap();
    // Doesn't import `k.inst`.
    std::fs::write(dir.join("k/user.ck"), "module k.user\n\nimport k.cls (Make)\n\nexport fn six -> r : r~Int, r == 6\n    Make.make 5\n").unwrap();
    std::fs::write(dir.join("main.ck"), "module main\n\nimport k.inst\nimport k.user (six)\n\ncheck six == six\n").unwrap();
    let (ok, first) = ckc_status(&dir, &["check", "main.ck"]);
    assert!(ok, "{first}");
    std::fs::write(dir.join("k/inst.ck"), inst("u", "u")).unwrap();
    let (ok, again) = ckc_status(&dir, &["check", "main.ck"]);
    assert!(!ok && again.contains("E0450"), "`six` is proved again, and fails:\n{again}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// The same through an operator: `<=` on a type with an `Ord` instance in a
/// module not imported.
#[test]
fn editing_an_unimported_operator_instance_forgets_its_user() {
    let dir = scratch("operator");
    std::fs::create_dir_all(dir.join("k")).unwrap();
    std::fs::write(dir.join("k/box.ck"), "module k.box\n\nexport record Box\n    n~Int\n").unwrap();
    let inst = |op: &str| {
        format!("module k.inst\n\nimport k.box (Box)\n\ninstance Ord Box\n    fn le x y -> r : x~Box, y~Box, r~Bool, r == (x.n {op} y.n)\n        x.n {op} y.n\n")
    };
    std::fs::write(dir.join("k/inst.ck"), inst("<=")).unwrap();
    // Doesn't import `k.inst`.
    std::fs::write(dir.join("k/user.ck"), "module k.user\n\nimport k.box (Box)\n\nexport fn ordered -> r : r~Bool, r\n    Box 1 <= Box 2\n").unwrap();
    std::fs::write(dir.join("main.ck"), "module main\n\nimport k.inst\nimport k.user (ordered)\n\ncheck ordered == ordered\n").unwrap();
    let (ok, first) = ckc_status(&dir, &["check", "main.ck"]);
    assert!(ok, "{first}");
    std::fs::write(dir.join("k/inst.ck"), inst(">=")).unwrap();
    let (ok, again) = ckc_status(&dir, &["check", "main.ck"]);
    assert!(!ok && again.contains("E0450"), "`ordered` is proved again, and fails:\n{again}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A module's own function proved while the module is checked, so that its
/// value is known there (§8.9), isn't proved again by the proofs phase: Z3
/// is asked about its obligation once. The check succeeds only if `SIZE`'s
/// value is known.
#[test]
fn proved_on_demand_once() {
    let dir = scratch("early");
    std::fs::write(
        dir.join("early.ck"),
        "module early\n\nimport std.array\n\nfn size k -> r : k~Nat, r~Int\n    let n = array.count 7 (array.repeat k 7)\n    if n >= 1 then array.count 7 (array.repeat (n - 1) 7) - 3 else 0\n\nlet SIZE = size 9\n\nfn by_constant k -> r : k~Int, r~Nat\n    if k < 0 then SIZE else 0\n",
    )
    .unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_ckc")).args(["check", "--no-cache", "early.ck"]).env("CHECKERS_SMT_DUMP", "1").current_dir(&dir).output().unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stdout));
    let dump = String::from_utf8_lossy(&out.stderr);
    // `(n - 1)`, at bytes 154 to 161.
    assert_eq!(dump.lines().filter(|l| l.starts_with(";; ── NatSub at Span { start: 154,")).count(), 1, "asked once:\n{dump}");
    let _ = std::fs::remove_dir_all(&dir);
}
