module equal_long

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)
import std.hint (blackbox)

# `==` takes stack independent of the values' size, as building them does:
# along a list (the last field) and along a chain nested in the first field.

enum Snoc
    Lin
    Snoc s n : s~Snoc, n~Nat

fn long n -> r : n~Nat, r~List Nat
    if n == 0 then [] else 1 :: long (n - 1)

fn snoc_onto s n -> r : s~Snoc, n~Nat, r~Snoc
    decreasing n
    if n == 0 then s else snoc_onto (Snoc s 1) (n - 1)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    # Sizes given through `blackbox`, so `==` runs when the program does.
    terminal.print_line (debug (long (blackbox 4000000) == long (blackbox 4000000))) sys.term
    terminal.print_line (debug (snoc_onto Lin (blackbox 4000000) == snoc_onto Lin (blackbox 4000000))) sys.term
    Success
