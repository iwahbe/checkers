module par_tuple_stress

# `par` whose last component is a tuple gives a flat tuple (#673, #562):
# `par (10, two 20)` is `(10, 21, 22)`, however it is taken apart.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)

fn two n -> r : n~Int, r~(Int, Int)
    (n + 1, n + 2)

fn names n -> r : n~Int, r~(String, String)
    ("b" ++ debug n, "c" ++ debug n)

fn line s term : s~String, term~Term
    terminal.print_line s term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    line (debug (par (10, two 20))) term
    line (debug (par (10, two 20) == (10, 21, 22))) term
    let (x, y, z) = par (10, two 20)
    line (debug y ++ " " ++ debug z ++ " " ++ debug (x + y + z)) term
    let (p, q, r) = par ("a", names 1)
    line (p ++ q ++ r) term
    let (u, v, w) = par (two 1, 3, two 4)
    let (a, b) = u
    let (c, d) = w
    line (debug (a + b + v + c + d)) term
    Success
