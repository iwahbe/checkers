module inline_call_error

# A runtime error in a small function whose body is placed where it is
# called (§14) names that function, not the caller.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

fn less n -> r : n~Nat, r~Nat
    10 - n

fn show n -> s : n~Nat, s~String
    debug (less n)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (show 3) sys.term
    terminal.print_line (show 12) sys.term
    Success
