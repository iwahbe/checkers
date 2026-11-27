module minmax

# Benchmark (§14): 200 million steps adding `min i k - max i k`, with `min`
# and `max` generic over `Ord` (used at `Int`), written for `Int`, and
# written out by hand in the loop. `minmax generic`, `minmax mono` or
# `minmax hand`; each prints the same.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)
import std.hint (blackbox)

fn min x y -> r : Ord a, x~a, y~a, r~a
    if x <= y then x else y

fn max x y -> r : Ord a, x~a, y~a, r~a
    if x >= y then x else y

fn imin x y -> r : x~Int, y~Int, r~Int
    if x <= y then x else y

fn imax x y -> r : x~Int, y~Int, r~Int
    if x >= y then x else y

fn generic k i acc -> r : k~Nat, i~Int, acc~Int, r~Int
    if k == 0 then acc else generic (k - 1) (i + 1) (acc + min i k - max i k)

fn mono k i acc -> r : k~Nat, i~Int, acc~Int, r~Int
    if k == 0 then acc else mono (k - 1) (i + 1) (acc + imin i k - imax i k)

fn hand k i acc -> r : k~Nat, i~Int, acc~Int, r~Int
    if k == 0 then acc else hand (k - 1) (i + 1) (acc + (if i <= k then i else k) - (if i >= k then i else k))

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    # Given through `blackbox`, so the work is done when the program runs,
    # not when it is compiled.
    let n = blackbox 200000000
    let r = match args
        ["generic"] -> generic n 0 0
        ["mono"]    -> mono n 0 0
        _           -> hand n 0 0
    terminal.print_line (debug r) sys.term
    Success
