module known_instance_error

# A runtime error in an instance's function called directly at a known
# instance (§14) names that function.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

class Down a
    fn down x -> n : x~a, n~Nat

instance Down (List a)
    fn down xs
        len xs - 3

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line "before" sys.term
    terminal.print_line (debug (down [1, 2])) sys.term
    Success
