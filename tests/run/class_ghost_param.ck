module class_ghost_param

# A class's function may take a `ghost` parameter: its field in the
# dictionary takes it erased, so the function is chosen by the type alone.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

class Sized a
    fn limit x -> n : x~ghost a, n~Nat

instance Sized Int
    fn limit x
        8

instance Sized Bool
    fn limit x
        1

fn by_clause x -> n : Sized a, x~ghost a, n~Nat
    Sized.limit x

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (debug (Sized.limit 3)) term
    terminal.print_line (debug (by_clause True)) term
    Success
