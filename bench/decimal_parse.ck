module decimal_parse

# Benchmark (§14): numbers read from 3 MB of bytes, by `Parsable`'s
# instance for `Decimal` (generic code over `Seq` and `Token`), and by a
# reader written for `Bytes` alone that takes the same numbers by index.
# `decimal_parse generic` or `decimal_parse mono`; both print the same.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (format)
import std.bytes
import std.decimal (Decimal, render, scaled)
import std.parse (Parsable)

# `n` copies of a line of numbers.
fn input n acc -> r : n~Nat, acc~List Bytes, r~Bytes
    decreasing n
    if n == 0 then bytes.concat acc else input (n - 1) (b"12345 -6.5 0.25 1e3 " :: acc)

# ── Generic: `Parsable.parse` on bytes ──

# How many numbers, and the last one; each is followed by one byte.
fn generic xs n last -> r : xs~Bytes, n~Nat, last~Decimal, r~(Nat, Decimal)
    decreasing len xs
    match Parsable.parse xs Decimal Int
        Ok (d, rest) ->
            match rest
                _ :: after -> generic after (n + 1) d
                []         -> (n + 1, d)
        Err _        -> (n, last)

# ── Hand-written: by index ──

fn digit xs i -> r : xs~Bytes, i~Nat, r~Bool
    i < len xs and xs[i] >= '0' and xs[i] <= '9'

# Digits read: their value, how many, and where they end.
record Digits
    value~Int
    count~Int
    stop~Nat

# The digits from `i`, after `m`.
fn digits xs i m k -> r : xs~Bytes, i~Nat, i <= len xs, m~Int, k~Int, r~Digits, r.stop <= len xs
    decreasing len xs - i
    if i < len xs and xs[i] >= '0' and xs[i] <= '9'
        digits xs (i + 1) (m * 10 + (xs[i] - '0')) (k + 1)
    else
        Digits m k i

# A number read, and where it ends.
record Read
    value~Decimal
    stop~Nat

# The number at `i`.
fn read xs i -> r : xs~Bytes, i~Nat, i < len xs, r~Read, r.stop <= len xs
    let neg = xs[i] == '-'
    let a = digits xs (if neg then i + 1 else i) 0 0
    let b = if a.stop < len xs and xs[a.stop] == '.'
        let f = digits xs (a.stop + 1) a.value 0
        Digits f.value (0 - f.count) f.stop
    else
        Digits a.value 0 a.stop
    let c = if b.stop < len xs and (xs[b.stop] == 'e' or xs[b.stop] == 'E')
        let x = digits xs (b.stop + 1) 0 0
        Digits b.value (b.count + x.value) x.stop
    else
        b
    Read (scaled (if neg then 0 - c.value else c.value) c.count) c.stop

fn mono xs i n last -> r : xs~Bytes, i~Nat, i <= len xs, n~Nat, last~Decimal, r~(Nat, Decimal)
    decreasing len xs - i
    if i < len xs and (digit xs i or xs[i] == '-')
        let r = read xs i
        if r.stop > i and r.stop < len xs then mono xs (r.stop + 1) (n + 1) r.value else (n + 1, r.value)
    else
        (n, last)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    let xs = input 150000 []
    let (n, last) = match args
        ["mono"] -> mono xs 0 0 (scaled 0 0)
        _        -> generic xs 0 (scaled 0 0)
    terminal.print_line format"{n} numbers, the last {render last}" term
    Success
