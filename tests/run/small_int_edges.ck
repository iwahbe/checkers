# Integer operations at the edges of a word's small integers (63 bits, from
# -2^62 to 2^62 - 1) and past them: inline code and the runtime agree, and a
# value known to be a small integer in one place isn't taken to be one in
# another.
module small_int_edges

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.string (debug)

fn line s term : s~String, term~Term
    terminal.print_line s term

fn ops x y -> s : x~Int, y~Int, s~String
    let sums = debug (x + y) ++ " " ++ debug (x - y) ++ " " ++ debug (x * y)
    let order = debug (x < y) ++ " " ++ debug (x <= y) ++ " " ++ debug (x == y) ++ " " ++ debug (x != y)
    sums ++ " " ++ order

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

# One operand a constant: only the other is tested.
fn by_constants x -> s : x~Int, s~String
    let a = debug (0 - x) ++ " " ++ debug (x + 1) ++ " " ++ debug (x - 1) ++ " " ++ debug (x * 2)
    let b = debug (x / 2) ++ " " ++ debug (x % 2) ++ " " ++ debug (x / (-1)) ++ " " ++ debug (x % 1000)
    let c = debug (x == 0) ++ " " ++ debug (x != 4611686018427387903) ++ " " ++ debug (x < 1)
    a ++ " " ++ b ++ " " ++ c

fn negate x -> r : x~Int, r~Int
    -x

# `x` is a small integer in the arm where `x == 3` holds, and not past it.
fn by_eq x -> r : x~Int, r~Int
    if x == 3 then x * x else x * 2

fn by_ne x -> r : x~Int, r~Int
    if x != 3 then x * 2 else x * x

fn by_literal x -> r : x~Int, r~Int
    match x
        0 -> x + 1
        _ -> x * x

# A remainder by a small integer is one, whatever it divides.
fn by_rem x -> r : x~Int, r~Int
    let m = x % 1000
    m * m + m

fn each xs term : xs~List Int, term~Term
    match xs
        []        -> ()
        x :: rest ->
            let s = by_constants x ++ " " ++ debug (negate x)
            let t = debug (by_eq x) ++ " " ++ debug (by_ne x) ++ " " ++ debug (by_literal x) ++ " " ++ debug (by_rem x)
            line (debug x ++ ": " ++ s ++ " " ++ t) term
            each rest term

fn down n -> s : n~Nat, s~String
    if n >= 1 then debug (n - 1) ++ " " ++ debug (n - n) else "0"

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    let edges = [0, 1, -3, 2147483648, -2147483648, 3037000500, 4611686018427387903, -4611686018427387904, 4611686018427387904, -4611686018427387905]
    pairs edges edges term
    each (edges ++ [3, 9223372036854775807, -9223372036854775808]) term
    line (down 1 ++ " " ++ down 4611686018427387903 ++ " " ++ down 4611686018427387904) term
    Success
