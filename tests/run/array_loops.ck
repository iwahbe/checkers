module array_loops

# Loops over arrays: bytes, slices of bytes, arrays of words (numbers and
# strings), packed arrays, at a type parameter, and `Bool`s matched as
# soon as they are made (`and`, `or`, a call's result, a `match`'s
# default arm). Each loop passes its arrays on unchanged.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)
import std.array
import std.bytes
import std.hint (blackbox)

# The first index from `i` where the bytes differ.
fn differ xs ys i -> r : xs~Bytes, ys~Bytes, i~Nat, i <= len xs, r~Nat
    decreasing len xs - i
    if i < len xs and i < len ys and xs[i] == ys[i] then differ xs ys (i + 1) else i

# The sum of `xs` from `i` on, after `acc`.
fn total xs i acc -> r : xs~Array Int, i~Nat, i <= len xs, acc~Int, r~Int
    decreasing len xs - i
    if i < len xs then total xs (i + 1) (acc + xs[i]) else acc

# The first index from `i` holding `x`, or `len xs`: at a type parameter.
fn find_from xs x i -> r : xs~Array a, x~a, i~Nat, i <= len xs, r~Nat
    decreasing len xs - i
    if i < len xs and not (xs[i] == x) then find_from xs x (i + 1) else i

# How many of `xs` from `i` on are short or a word, after `n`.
fn count_short xs i n -> r : xs~Array String, i~Nat, i <= len xs, n~Nat, r~Nat
    decreasing len xs - i
    if i < len xs
        count_short xs (i + 1) (if len (string.bytes xs[i]) < 3 or is_word xs[i] then n + 1 else n)
    else
        n

# A `Bool` a call gives.
fn is_word s -> r : s~String, r~Bool
    blackbox (s == "word")

# A `Bool` from a `match` with a default arm, matched at once.
fn small_tag n -> r : n~Int, r~Nat
    let b = match n
        0 -> True
        1 -> blackbox False
        _ -> n < 0
    if b then 1 else 2

fn line n term : n~Int, term~Term
    terminal.print_line (debug n) term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    let xs = blackbox b"abcdefgh"
    let ys = blackbox b"abcdXfgh"
    line (differ xs ys 0) term
    line (differ xs xs 0) term
    line (differ (bytes.slice xs 2 8) (bytes.slice ys 2 8) 0) term
    line (differ b"" ys 0) term
    line (total (blackbox (array.from_list [1, 2, 3, 40000000000000000000])) 0 0) term
    line (total (blackbox (array.slice (array.from_list [5, 6, 7, 8]) 1 3)) 0 0) term
    line (find_from xs 'e' 0) term
    line (find_from (blackbox (array.from_list [10, 20, 30])) 30 0) term
    line (find_from (blackbox (array.from_list [True, True, False])) False 0) term
    line (find_from (blackbox (array.from_list ["a", "b"])) "c" 0) term
    line (count_short (blackbox (array.from_list ["ab", "word", "three", "x"])) 0 0) term
    line (small_tag (blackbox 0)) term
    line (small_tag (blackbox 1)) term
    line (small_tag (blackbox (-4))) term
    line (small_tag (blackbox 9)) term
    Success
