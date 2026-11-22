module inline_match_error

# A runtime error in a function whose result a `match` resolves at compile
# time (§14) names that function, not the caller.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

fn less n -> r : n~Nat, r~Option Nat
    if n == 0 then None else Some (10 - n)

fn show n -> s : n~Nat, s~String
    match less n
        None   -> "none"
        Some m -> debug m

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (show 3) sys.term
    terminal.print_line (show 12) sys.term
    Success
