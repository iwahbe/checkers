module instance_pinned_context

# An instance's function passes its own type variable to a class's
# function that takes the class's parameter explicitly: the type is
# erased there, so the instance builds on its context's instance.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

class Make t
    fn make x t -> r : x~Int, t~ghost Type, r~Option t

instance Make Int
    fn make x t
        Some x

instance Make (List a) : Make a
    fn make x t
        match Make.make x a
            Some v -> Some [v]
            None   -> None

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (debug (Make.make 5 (List (List Int)))) term
    Success
