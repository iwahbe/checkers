module unproved_bounds

# With `--unverified`, a bound a signature gives isn't proved, so code
# doesn't rely on it: numbers past the bounds still add up, and a division
# by zero still stops the program. Each function is too big to be inlined.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)

fn add_bytes a b c d -> r : a~U8, b~U8, c~U8, d~U8, r~Nat
    (a + b) + (c + d) + (a + c) + (b + d)

fn halves a b -> r : a~U16, b~U16, 1 <= b, r~Int
    a / b + a % b - (-a) + a / b * (a % b)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let big = 4611686018427387903
    terminal.print_line (debug (add_bytes big big big big)) sys.term
    terminal.print_line (debug (halves 7 0)) sys.term
    Success
