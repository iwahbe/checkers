module inline_match_error

# A runtime error in a function whose result a `match` resolves at compile
# time (§14) names that function, not the caller. The subtraction rests on
# an `admit`, so it is checked (§13.3).

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

lemma small n : n~Nat
    ensures n <= 10
    proof
        admit

fn less n -> r : n~Nat, r~Option Nat
    have small n
    if n == 0 then None else Some (10 - n)

fn show n -> s : n~Nat, s~String
    match less n
        None   -> "none"
        Some m -> debug m

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (show 3) sys.term
    terminal.print_line (show 12) sys.term
    Success
