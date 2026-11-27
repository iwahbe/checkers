//! Known values are kept across builds in `.checkers/` beside the checked
//! file (SPEC §8.9): computed once, reused while nothing they can run has
//! changed, computed again when something has.

use std::path::{Path, PathBuf};
use std::process::Command;

/// `ckc run` on `p.ck` in `dir`, with the cache on: its output, and the
/// known values it computed rather than reused.
fn run(dir: &Path) -> (String, Vec<String>) {
    let out = Command::new(env!("CARGO_BIN_EXE_ckc"))
        .args(["run", "p.ck"])
        .current_dir(dir)
        .env_remove("CHECKERS_NO_CACHE")
        .env("CHECKERS_KNOWN_TRACE", "1")
        .output()
        .expect("run ckc");
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(out.status.success(), "{stderr}");
    let computed = stderr.lines().filter_map(|l| l.strip_prefix("known value computed: ")).map(str::to_string).collect();
    (String::from_utf8_lossy(&out.stdout).into_owned(), computed)
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("checkers-known-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// A constant whose value native code computes when compiling (a list,
/// which the type checker's own evaluation doesn't give), and a function
/// it never runs.
fn program(element: &str, other: &str) -> String {
    format!(
        "module p

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

fn build n -> r : n~Nat, r~List Nat
    decreasing n
    if n == 0 then [] else {element} :: build (n - 1)

fn other x -> r : x~Nat, r~Nat
    {other}

let LIST = build 3

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug LIST) sys.term
    terminal.print_line (debug (other (len args))) sys.term
    Success
"
    )
}

#[test]
fn known_values_are_kept_across_builds() {
    let dir = scratch("kept");
    std::fs::write(dir.join("p.ck"), program("7", "x + 1")).unwrap();
    let (out, computed) = run(&dir);
    assert_eq!(out, "[7, 7, 7]\n1\n");
    assert!(computed.iter().any(|c| c == "LIST"), "the first build computes `LIST`: {computed:?}");

    let (out, computed) = run(&dir);
    assert_eq!(out, "[7, 7, 7]\n1\n");
    assert!(computed.is_empty(), "the next build reuses every value, but computed {computed:?}");

    // A function the value doesn't run: still reused.
    std::fs::write(dir.join("p.ck"), program("7", "x + 2")).unwrap();
    let (out, computed) = run(&dir);
    assert_eq!(out, "[7, 7, 7]\n2\n");
    assert!(computed.is_empty(), "an edit elsewhere keeps it, but computed {computed:?}");

    // The function that computes it: computed again, with its new value.
    std::fs::write(dir.join("p.ck"), program("8", "x + 2")).unwrap();
    let (out, computed) = run(&dir);
    assert_eq!(out, "[8, 8, 8]\n2\n");
    // Folding computes again only what uses the new value: `debug LIST`.
    let (folded, checker): (Vec<_>, Vec<_>) = computed.iter().partition(|c| c.ends_with(", folded"));
    assert_eq!(checker, ["LIST"], "an edit of `build` computes `LIST` again, and only it");
    assert!(folded.iter().all(|c| c.contains("`debug`")), "an edit of `build` folds again only what uses `LIST`: {folded:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A call folding computes in a function's body (not a constant), and a
/// function it never runs.
fn folding(element: &str, other: &str) -> String {
    format!(
        "module p

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

fn build n -> r : n~Nat, r~List Nat
    decreasing n
    if n == 0 then [] else {element} :: build (n - 1)

fn other x -> r : x~Nat, r~Nat
    {other}

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (build 3)) sys.term
    terminal.print_line (debug (other (len args))) sys.term
    Success
"
    )
}

#[test]
fn folded_values_are_kept_across_builds() {
    let dir = scratch("folded");
    let folded = |computed: &[String]| computed.iter().filter(|c| c.ends_with(", folded")).cloned().collect::<Vec<_>>();
    std::fs::write(dir.join("p.ck"), folding("7", "x + 1")).unwrap();
    let (out, computed) = run(&dir);
    assert_eq!(out, "[7, 7, 7]\n1\n");
    let first = folded(&computed);
    assert!(first.iter().any(|c| c.contains("`build`")), "the first build folds the call of `build`: {computed:?}");

    let (out, computed) = run(&dir);
    assert_eq!(out, "[7, 7, 7]\n1\n");
    assert!(computed.is_empty(), "the next build reuses every value, but computed {computed:?}");

    // A function the call doesn't run: still reused.
    std::fs::write(dir.join("p.ck"), folding("7", "x + 2")).unwrap();
    let (out, computed) = run(&dir);
    assert_eq!(out, "[7, 7, 7]\n2\n");
    assert!(computed.is_empty(), "an edit elsewhere keeps it, but computed {computed:?}");

    // The function it runs: computed again, with its new value, and
    // nothing else is.
    std::fs::write(dir.join("p.ck"), folding("8", "x + 2")).unwrap();
    let (out, computed) = run(&dir);
    assert_eq!(out, "[8, 8, 8]\n2\n");
    assert_eq!(folded(&computed), first, "an edit of `build` computes again what runs it, and only that");
    assert_eq!(folded(&computed).len(), computed.len(), "an edit of `build` computes no other value: {computed:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A type the type checker's own evaluation computes from a `comptime`
/// argument, long enough to be kept (more than a thousand unfoldings),
/// and a function it never runs.
fn computed_type(base: &str, other: &str) -> String {
    let text = "a".repeat(1500);
    format!(
        "module p

import std.system (System, ExitCode)
import std.terminal
import std.string

fn walk src i -> t : src~Bytes, i~Nat, i <= len src, t~Type
    decreasing len src - i
    if i == len src
        {base}
    else if src[i] == '{{'
        String
    else
        walk src (i + 1)

fn pick s x -> y : s~comptime String, x~walk (string.bytes s) 0, y~walk (string.bytes s) 0
    x

fn other x -> r : x~Nat, r~Nat
    {other}

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (pick \"{text}{{\" \"kept\") sys.term
    terminal.print_line (string.debug (other (len args))) sys.term
    Success
"
    )
}

#[test]
fn computed_types_are_kept_across_builds() {
    let dir = scratch("types");
    let walk = |computed: &[String]| computed.iter().filter(|c| c.starts_with("walk ")).cloned().collect::<Vec<_>>();
    std::fs::write(dir.join("p.ck"), computed_type("Int", "x + 1")).unwrap();
    let (out, computed) = run(&dir);
    assert_eq!(out, "kept\n1\n");
    let first = walk(&computed);
    assert!(!first.is_empty(), "the first build computes the type: {computed:?}");

    let (out, computed) = run(&dir);
    assert_eq!(out, "kept\n1\n");
    assert!(computed.is_empty(), "the next build reuses every value, but computed {computed:?}");

    // A function the type doesn't run: still reused.
    std::fs::write(dir.join("p.ck"), computed_type("Int", "x + 2")).unwrap();
    let (out, computed) = run(&dir);
    assert_eq!(out, "kept\n2\n");
    assert!(computed.is_empty(), "an edit elsewhere keeps it, but computed {computed:?}");

    // The function that computes it: computed again, and nothing else is.
    std::fs::write(dir.join("p.ck"), computed_type("Nat", "x + 2")).unwrap();
    let (out, computed) = run(&dir);
    assert_eq!(out, "kept\n2\n");
    assert_eq!(computed, first, "an edit of `walk` computes the type again, and only it");
    let _ = std::fs::remove_dir_all(&dir);
}
