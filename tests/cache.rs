//! Z3's answers are cached (D100): a second check reuses them, an entry
//! whose query doesn't match exactly is ignored, and `--no-cache` neither
//! reads nor writes the cache.

use std::path::{Path, PathBuf};
use std::process::Command;

fn ckc(dir: &Path, args: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_ckc")).args(args).current_dir(dir).output().expect("run ckc");
    assert!(out.status.success(), "ckc {args:?}: {}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("checkers-cache-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    std::fs::copy(root.join("examples/sort.ck"), dir.join("sort.ck")).unwrap();
    dir
}

fn cache_line(ledger: &str) -> Option<String> {
    ledger.lines().find(|l| l.starts_with("cache: ")).map(str::to_string)
}

/// The ledger without its cache line: the same, cached or not.
fn proofs(ledger: &str) -> String {
    ledger.lines().filter(|l| !l.starts_with("cache: ")).map(|l| format!("{l}\n")).collect()
}

#[test]
fn second_check_reuses_answers() {
    let dir = scratch("reuse");
    let first = ckc(&dir, &["trust", "sort.ck"]);
    assert_eq!(cache_line(&first), None, "nothing cached yet:\n{first}");
    let second = ckc(&dir, &["trust", "sort.ck"]);
    let line = cache_line(&second).expect("a cache line");
    let nums: Vec<&str> = line.split_whitespace().filter(|w| w.parse::<usize>().is_ok()).collect();
    assert_eq!(nums.len(), 2, "{line}");
    assert_eq!(nums[0], nums[1], "every answer reused: {line}");
    assert_eq!(proofs(&first), proofs(&second));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn mismatched_entry_is_ignored() {
    let dir = scratch("mismatch");
    let first = ckc(&dir, &["trust", "sort.ck"]);
    // Change one byte of each stored query: as a hash collision would look.
    for e in std::fs::read_dir(dir.join(".checkers/z3")).unwrap() {
        let p = e.unwrap().path();
        let text = std::fs::read_to_string(&p).unwrap();
        let (header, rest) = text.split_once('\n').unwrap();
        let changed = rest.replacen("(set-logic ALL)", "(set-logic ALl)", 1);
        std::fs::write(&p, format!("{header}\n{changed}")).unwrap();
    }
    let again = ckc(&dir, &["trust", "sort.ck"]);
    assert_eq!(cache_line(&again), None, "no entry matches:\n{again}");
    assert_eq!(proofs(&first), proofs(&again));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn no_cache_flag() {
    let dir = scratch("off");
    ckc(&dir, &["trust", "--no-cache", "sort.ck"]);
    assert!(!dir.join(".checkers").exists());
    let _ = std::fs::remove_dir_all(&dir);
}
