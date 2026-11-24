module fn_copies_error

# A runtime error in a lambda that a copy of a function specialized to it
# (§14) runs names the function the lambda is written in.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

fn apply f x -> r : f~(Nat -> Nat), x~Nat, r~Nat
    f x

fn less n -> r : n~Nat, r~Nat
    apply (\x -> x - n) 10

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line "before" sys.term
    terminal.print_line (debug (less 12)) sys.term
    Success
