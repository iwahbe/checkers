module monoid_fold

# Benchmark (§14): a fold, generic over `Monoid` and `Add`, at `Int` and at
# a record of two numbers with instances of its own, and the same fold
# written for each type. `monoid_fold generic` or `monoid_fold mono`; both
# print the same.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (format)

# Two running totals.
record Pair
    a~Int
    b~Int

instance Add Pair
    fn add x y
        Pair (x.a + y.a) (x.b + y.b)

instance Monoid Pair
    fn zero
        Pair 0 0

fn numbers n acc -> r : n~Nat, acc~List Int, r~List Int
    decreasing n
    if n == 0 then acc else numbers (n - 1) (n % 1000 :: acc)

fn pairs xs -> r : xs~List Int, r~List Pair
    match xs
        []        -> []
        x :: rest -> Pair x (x * 2) :: pairs rest

# ── Generic ──

fn fold xs acc -> r : Monoid a, Add a, xs~List a, acc~a, r~a
    match xs
        []        -> acc
        x :: rest -> fold rest (acc + x)

# Each list `k` more times.
fn repeat xs k acc -> r : Monoid a, Add a, xs~List a, k~Nat, acc~a, r~a
    decreasing k
    if k == 0 then acc else repeat xs (k - 1) (acc + fold xs zero)

# ── Written for each type ──

fn fold_int xs acc -> r : xs~List Int, acc~Int, r~Int
    match xs
        []        -> acc
        x :: rest -> fold_int rest (acc + x)

fn repeat_int xs k acc -> r : xs~List Int, k~Nat, acc~Int, r~Int
    decreasing k
    if k == 0 then acc else repeat_int xs (k - 1) (acc + fold_int xs 0)

fn fold_pair xs acc -> r : xs~List Pair, acc~Pair, r~Pair
    match xs
        []        -> acc
        x :: rest -> fold_pair rest (Pair (acc.a + x.a) (acc.b + x.b))

fn repeat_pair xs k acc -> r : xs~List Pair, k~Nat, acc~Pair, r~Pair
    decreasing k
    if k == 0
        acc
    else
        let s = fold_pair xs (Pair 0 0)
        repeat_pair xs (k - 1) (Pair (acc.a + s.a) (acc.b + s.b))

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    # Unknown when compiling (`none` is 0), so the work is done when the
    # program runs, not when it is compiled (§8.9).
    let none = len args - len args
    let xs = numbers (none + 100000) []
    let ps = pairs xs
    let (n, p) = match args
        ["mono"] -> (repeat_int xs 100 0, repeat_pair ps 100 (Pair 0 0))
        _        -> (repeat xs 100 zero, repeat ps 100 zero)
    terminal.print_line format"{n} {p.a} {p.b}" term
    Success
