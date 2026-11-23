module decimal

# Benchmark: a million numbers of 7 to 13 digits written in decimal, three
# ways: `builtin` (`display`, which the runtime writes), `literal` (Checkers
# code dividing by ten, a one-byte string literal per digit, `++`) and `char`
# (the same, each digit made by `string.from_char`). Run each with
# `ckc build --release` and compare; Checkers code should be close to the
# builtin.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.char
import std.string (format, display)

# `n` in decimal, each digit a string literal.
fn by_literal n -> s : n~Nat, s~String
    decreasing n
    if n < 10
        literal n
    else
        let a = by_literal (n / 10)
        let c = literal (n % 10)
        a ++ c

# `n` in decimal, each digit made from its character.
fn by_char n -> s : n~Nat, s~String
    decreasing n
    if n < 10
        from_char n
    else
        let a = by_char (n / 10)
        let c = from_char (n % 10)
        a ++ c

# A digit as a string literal.
fn literal d -> s : d~Nat, s~String
    if d < 5
        if d == 0 then "0" else if d == 1 then "1" else if d == 2 then "2" else if d == 3 then "3" else "4"
    else
        if d == 5 then "5" else if d == 6 then "6" else if d == 7 then "7" else if d == 8 then "8" else "9"

# A digit as a string of its character.
fn from_char d -> s : d~Nat, s~String
    if d < 10 then string.from_char (char.from_ascii ('0' + d)) else "?"

# `acc` and the total length of `k` numbers from the `i`th on, written by `write`.
fn total i k write acc -> t : i~Nat, k~Nat, write~(Nat -> String), acc~Nat, t~Nat
    decreasing k
    if k > 0
        let s = write (1234567 + i * 987654)
        total (i + 1) (k - 1) write (acc + len s.bytes)
    else
        acc

fn run write term -> code : write~(Nat -> String), term~Term, code~ExitCode
    let t = total 0 1000000 write 0
    terminal.print_line format"{t}" term
    Success

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    match args
        ["builtin"] -> run (\n -> display n []) term
        ["literal"] -> run (\n -> by_literal n) term
        ["char"]    -> run (\n -> by_char n) term
        _           ->
            terminal.eprint_line "usage: decimal builtin|literal|char" term
            Failure 2
