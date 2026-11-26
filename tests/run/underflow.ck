module underflow

# A `Nat` subtraction proved only from an `admit` is checked at run time
# (§13.3): going below zero stops the program.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

lemma at_least n : n~Nat
    ensures n >= 3
    proof
        admit

fn steps n -> m : n~Nat, m~Nat
    have at_least n
    n - 3

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line "before" sys.term
    terminal.print_line (debug (steps 2)) sys.term
    Success
