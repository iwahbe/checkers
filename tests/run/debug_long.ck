module debug_long

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

# `debug` takes stack independent of the value's size: along a chain in the
# last field and along one in the first.

enum Chain
    End
    Link n c : n~Nat, c~Chain

enum Snoc
    Lin
    Snoc s n : s~Snoc, n~Nat

fn chain n -> r : n~Nat, r~Chain
    if n == 0 then End else Link 1 (chain (n - 1))

fn snoc_onto s n -> r : s~Snoc, n~Nat, r~Snoc
    decreasing n
    if n == 0 then s else snoc_onto (Snoc s 1) (n - 1)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (len (debug (chain 1000000)).bytes)) sys.term
    terminal.print_line (debug (len (debug (snoc_onto Lin 1000000)).bytes)) sys.term
    terminal.print_line (debug (chain 2)) sys.term
    terminal.print_line (debug (snoc_onto Lin 2)) sys.term
    Success
