module class_alias

# A class used at a refinement alias runs the instance of the type the
# alias stands for, directly, explicitly and through a clause.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)

class Make t
    fn make u -> r : u~Int, r~t

instance Make Int
    fn make u -> r : u~Int, r~Int, r >= 0
        if u >= 1 then u - 1 else 0

class Read t
    fn read x t -> r : x~Int, t~ghost Type, r~Option t

instance Read Int
    fn read x t -> r : x~Int, t~ghost Type, r~Option Int,
                       match r
                           Some v -> v == x * 2
                           None   -> True
        Some (x * 2)

fn made u -> r : Make t, u~Int, r~t
    make u

fn at_nat u -> n : u~Int, n~Nat
    make u

fn twice u -> n : u~Int, n~Nat
    made u + made u

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (debug (at_nat 5)) term
    terminal.print_line (debug (at_nat (-5))) term
    terminal.print_line (debug (twice 3)) term
    match Read.read 3 Nat
        Some v -> terminal.print_line (debug v) term
        None   -> terminal.print_line "none" term
    Success
