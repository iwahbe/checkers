module const_call

# A top-level constant may call a function declared in the same module,
# before or after it (found 11/06/2026: its type was silently unknown).

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)

let ANSWER = double 21
let GREETING = shout "hi"

fn double n -> m : n~Nat, m~Nat
    2 * n

fn shout s -> t : s~String, t~String
    s ++ "!"

check ANSWER == 42

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug ANSWER ++ " " ++ GREETING) sys.term
    Success
