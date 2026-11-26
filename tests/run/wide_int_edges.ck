# Integer operations on numbers past a word but within 128 bits, at the
# edges: a small integer's (±2^62), 64 bits' (±2^63, ±2^64) and 128 bits'
# (±2^127). A result that fits in a word is a small integer again; one past
# 128 bits is a big number. `/` and `%` are Euclidean whatever the signs,
# computed together (`paired`) or alone.
module wide_int_edges

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.string (debug)

fn line s term : s~String, term~Term
    terminal.print_line s term

fn quotient x y -> r : x~Int, y~Int, y != 0, r~Int
    x / y

fn remainder x y -> r : x~Int, y~Int, y != 0, r~Int
    x % y

fn paired x y -> s : x~Int, y~Int, y != 0, s~String
    debug (x / y) ++ " " ++ debug (x % y)

fn ops x y -> s : x~Int, y~Int, s~String
    let sums = debug (x + y) ++ " " ++ debug (x - y) ++ " " ++ debug (x * y) ++ " " ++ debug (-x)
    let order = debug (x < y) ++ " " ++ debug (x <= y) ++ " " ++ debug (x == y) ++ " " ++ debug (x != y)
    let divs = if y == 0 then "-" else paired x y ++ " " ++ debug (quotient x y) ++ " " ++ debug (remainder x y)
    sums ++ " | " ++ order ++ " | " ++ divs

fn with_each x ys term : x~Int, ys~List Int, term~Term
    match ys
        []        -> ()
        y :: rest ->
            line (debug x ++ " " ++ debug y ++ ": " ++ ops x y) term
            with_each x rest term

fn pairs xs ys term : xs~List Int, ys~List Int, term~Term
    match xs
        []        -> ()
        x :: rest ->
            with_each x ys term
            pairs rest ys term

# `2^k`, computed: equal to a literal, though a different object.
fn power k -> r : k~Nat, r~Int
    decreasing k
    if k == 0 then 1 else 2 * power (k - 1)

fn down a b -> s : a~Nat, b~Nat, s~String
    if a >= b then debug (a - b) else "below"

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    let edges = [0, 7, -7, 4611686018427387904, -4611686018427387905, 9223372036854775808, -9223372036854775808, 18446744073709551616, -18446744073709551616, 170141183460469231731687303715884105727, -170141183460469231731687303715884105728, 170141183460469231731687303715884105728]
    pairs edges edges term
    line (debug (power 64 == 18446744073709551616) ++ " " ++ debug (power 127 - 1 == 170141183460469231731687303715884105727) ++ " " ++ debug (power 100 / power 50)) term
    line (down 18446744073709551616 9223372036854775808 ++ " " ++ down 9223372036854775808 18446744073709551616 ++ " " ++ down 340282366920938463463374607431768211456 1) term
    Success
