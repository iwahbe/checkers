module known_instance_error

# A runtime error in an instance's function called directly at a known
# instance (§14) names that function. The subtraction rests on an
# `admit`, so it is checked (§13.3).

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

class Down a
    fn down x -> n : x~a, n~Nat

lemma long xs : xs~List a
    ensures len xs >= 3
    proof
        admit

instance Down (List a)
    fn down xs
        have long xs
        len xs - 3

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line "before" sys.term
    terminal.print_line (debug (down [1, 2])) sys.term
    Success
