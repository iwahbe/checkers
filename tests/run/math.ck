module math

# `std.math` on small numbers and past a machine word.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)
import std.math

fn line s term : s~String, term~Term
    terminal.print_line s term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    line (debug (math.min 3 (-4)) ++ " " ++ debug (math.max 3 (-4))) term
    line (debug (math.min (math.pow 2 70) (math.pow 3 50))) term
    line (debug (math.max (math.pow 2 70) (math.pow 3 50))) term
    line (debug (math.pow 2 62) ++ " " ++ debug (math.pow 2 63) ++ " " ++ debug (math.pow 2 64)) term
    line (debug (math.pow (-3) 41)) term
    line (debug (math.pow 7 0) ++ " " ++ debug (math.pow 0 5)) term
    Success
