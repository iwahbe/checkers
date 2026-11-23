# `/` and `%` are Euclidean (the remainder is never negative) for every sign,
# small numbers and large, and at the edge of what fits in a word (§14).
module division

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.string (debug)

fn show a b term : a~Int, b~Int, b != 0, term~Term
    terminal.print_line (debug a ++ " / " ++ debug b ++ " = " ++ debug (a / b) ++ ", % " ++ debug (a % b)) term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    show 7 2 term
    show (-7) 2 term
    show 7 (-2) term
    show (-7) (-2) term
    show 6 (-3) term
    show (-6) 3 term
    show 0 (-5) term
    show 1234567890123 10 term
    # The smallest number in a word, and one past the largest.
    show (-4611686018427387904) (-1) term
    show (-4611686018427387904) 1 term
    show 4611686018427387904 (-1) term
    show 4611686018427387903 4611686018427387903 term
    show (-4611686018427387904) 4611686018427387903 term
    Success
