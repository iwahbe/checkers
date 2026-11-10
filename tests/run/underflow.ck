module underflow

# Until the prover exists, `-` on `Nat` is checked at run time (§13.3).

import std.system (System, ExitCode)
import std.terminal

fn steps n -> m : n~Nat, m~Nat
    n - 3

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line "before" sys.term
    terminal.print_line (format (steps 2)) sys.term
    Success
