module at_compare

# Code put into a function from another (`near` and `wrap` inlined, each
# with a `%` that could fail) gives the same results as the same code
# written there, at the edges of small integers too. `pick` and `step` are
# too big to be inlined themselves.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)

fn near x y -> r : x~Int, y~Int, r~Bool
    x % 7 <= y

fn pick x y -> r : x~Int, y~Int, r~Int
    if near x y then (if near y x then 0 else x) else (if near 0 y then y else x)

fn pick_int x y -> r : x~Int, y~Int, r~Int
    if x % 7 <= y then (if y % 7 <= x then 0 else x) else (if 0 % 7 <= y then y else x)

fn wrap x -> r : x~Int, r~Int
    x % 5

fn step x y -> r : x~Int, y~Int, r~Int
    (wrap x + 1) * (wrap y + 2) + (wrap x - wrap y)

fn step_int x y -> r : x~Int, y~Int, r~Int
    (x % 5 + 1) * (y % 5 + 2) + (x % 5 - y % 5)

fn line a b sys : a~Int, b~Int, sys~System
    let s = debug (pick a b) ++ " " ++ debug (pick_int a b) ++ " " ++ debug (step a b) ++ " " ++ debug (step_int a b)
    terminal.print_line s sys.term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    line 3 4 sys
    line 4 3 sys
    line (-5) (-5) sys
    line 4611686018427387904 4611686018427387903 sys
    line (-4611686018427387905) 0 sys
    Success
