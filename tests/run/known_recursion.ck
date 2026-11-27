module known_recursion

# Recursion on a known value makes one copy, not one per step: the copy
# for `n == 3` calls the general `down` with `2`.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)
import std.hint (blackbox)

fn down n x -> r : n~Nat, x~Int, r~Int
    decreasing n
    if n == 0 then x else down (n - 1) (x + n)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (down 3 (blackbox 10))) sys.term
    Success
