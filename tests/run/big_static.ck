module big_static

# Numbers past a word, written in the program or computed when it is
# compiled, are static data: past 128 bits too, of either sign.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)

enum Box
    Box n : n~Int

fn power b e -> r : b~Int, e~Nat, r~Int
    decreasing e
    if e == 0 then 1 else b * power b (e - 1)

fn boxed n -> r : n~comptime Int, r~Box
    Box n

fn unbox b -> n : b~Box, n~Int
    match b
        Box n -> n

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (debug 340282366920938463463374607431768211457) term
    terminal.print_line (debug (-340282366920938463463374607431768211457)) term
    terminal.print_line (debug (170141183460469231731687303715884105727 + 1)) term
    terminal.print_line (debug (unbox (boxed (power 3 100)))) term
    terminal.print_line (debug (unbox (boxed (-(power 2 70))))) term
    Success
