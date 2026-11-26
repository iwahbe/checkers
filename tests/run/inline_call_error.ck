module inline_call_error

# A runtime error in a small function whose body is placed where it is
# called (§14) names that function, not the caller. The subtraction rests
# on an `admit`, so it is checked (§13.3).

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

lemma small n : n~Nat
    ensures n <= 10
    proof
        admit

fn less n -> r : n~Nat, r~Nat
    have small n
    10 - n

fn show n -> s : n~Nat, s~String
    debug (less n)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (show 3) sys.term
    terminal.print_line (show 12) sys.term
    Success
