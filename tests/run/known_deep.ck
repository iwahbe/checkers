module known_deep

# A value a million constructors deep, computed at compile time, is static
# data in the program: laid out without recursion, and read when it runs.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)

enum Chain
    End
    Link c n : c~Chain, n~Nat

fn grow c n -> r : c~Chain, n~Nat, r~Chain
    decreasing n
    if n == 0 then c else grow (Link c n) (n - 1)

fn known c -> r : c~comptime Chain, r~Chain
    c

fn sum c acc -> n : c~Chain, acc~Nat, n~Nat
    match c
        End      -> acc
        Link r k -> sum r (acc + k)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (sum (known (grow End 1000000)) 0)) sys.term
    Success
