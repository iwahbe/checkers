//! `++` after a recursive call, made tail recursion (SPEC §14, `f.acc`),
//! takes time in proportion to the result: four times the pieces take about
//! four times as long, not sixteen, for strings, bytes, arrays and lists.

use std::path::Path;
use std::process::Command;

/// A program appending `n` pieces after a recursive call, `reps` times.
/// `ty` is the type, `base` the base case's value, `piece` the piece and
/// `len` the length of a value `v` of the type.
fn program(ty: &str, base: &str, piece: &str, len: &str, n: usize, reps: usize) -> String {
    format!(
        "module grow

import std.system (System, ExitCode)
import std.terminal
import std.array
import std.string (debug)

fn build n piece -> r : n~Nat, piece~{ty}, r~{ty}
    if n == 0 then {base} else build (n - 1) piece ++ piece

fn length v -> k : v~{ty}, k~Nat
    {len}

fn total k piece -> t : k~Nat, piece~{ty}, t~Nat
    if k == 0 then 0 else length (build {n} piece) + total (k - 1) piece

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (total {reps} {piece})) sys.term
    Success
"
    )
}

/// The time the program for `n` pieces takes to run, in seconds: the
/// fastest of three runs, the least disturbed by other tests.
fn run_time(dir: &Path, case: &Case, n: usize) -> f64 {
    let name = format!("{}{n}", case.name);
    std::fs::write(dir.join(format!("{name}.ck")), program(case.ty, case.base, case.piece, case.len, n, REPS)).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_ckc"))
        .args(["build", &format!("{name}.ck"), "-o", &name])
        .current_dir(dir)
        .env("CHECKERS_NO_CACHE", "1")
        .output()
        .expect("run ckc");
    assert!(out.status.success(), "{name}: {}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    (0..3)
        .map(|_| {
            let start = std::time::Instant::now();
            let out = Command::new(dir.join(&name)).env("CHECKERS_THREADS", "1").output().expect("run the program");
            let t = start.elapsed().as_secs_f64();
            let shown = String::from_utf8_lossy(&out.stdout);
            assert_eq!(shown.trim(), (REPS * case.each * (n + case.base_len)).to_string(), "{name}: {}", String::from_utf8_lossy(&out.stderr));
            t
        })
        .fold(f64::INFINITY, f64::min)
}

const REPS: usize = 5;

struct Case {
    name: &'static str,
    ty: &'static str,
    base: &'static str,
    /// The base case's length, in pieces.
    base_len: usize,
    piece: &'static str,
    /// A piece's length.
    each: usize,
    len: &'static str,
}

/// Four times the pieces may take at most ten times as long: quadratic work
/// takes sixteen times. (Times below 20 ms don't count.)
fn assert_linear(case: Case, small: usize) {
    let dir = std::env::temp_dir().join(format!("checkers-tailrec-scaling-{}-{}", std::process::id(), case.name));
    std::fs::create_dir_all(&dir).unwrap();
    let t_small = run_time(&dir, &case, small);
    let t_large = run_time(&dir, &case, 4 * small);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        t_large < 10.0 * t_small.max(0.02),
        "{}: {small} pieces took {:.0} ms, {} took {:.0} ms",
        case.name,
        t_small * 1000.0,
        4 * small,
        t_large * 1000.0
    );
}

#[test]
fn strings() {
    assert_linear(Case { name: "strings", ty: "String", base: "\"\"", base_len: 0, piece: "\"ab\"", each: 2, len: "len v.bytes" }, 40000);
}

#[test]
fn bytes() {
    let piece = "(string.bytes \"ab\")";
    assert_linear(Case { name: "bytes", ty: "Bytes", base: "piece", base_len: 1, piece, each: 2, len: "len v" }, 40000);
}

#[test]
fn arrays() {
    let piece = "(array.from_list [300, 7])";
    assert_linear(Case { name: "arrays", ty: "Array Int", base: "array.from_list []", base_len: 0, piece, each: 2, len: "len v" }, 2500);
}

#[test]
fn lists() {
    assert_linear(Case { name: "lists", ty: "List Nat", base: "piece", base_len: 1, piece: "[1, 2]", each: 2, len: "len v" }, 40000);
}
