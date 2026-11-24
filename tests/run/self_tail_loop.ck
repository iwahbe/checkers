# A function calling itself in tail position runs as a loop (§14): many
# steps in constant stack, its arguments passed all at once, so swapping
# them swaps them, as the call would.
module self_tail_loop

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.string (debug)

fn swap a b k -> r : a~String, b~String, k~Nat, r~(String, String)
    decreasing k
    if k == 0 then (a, b) else swap b a (k - 1)

fn count k acc -> r : k~Nat, acc~Nat, r~Nat
    decreasing k
    if k == 0 then acc else count (k - 1) (acc + k % 3)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (debug (swap "a" "b" 3) ++ " " ++ debug (swap "a" "b" 1000000)) term
    terminal.print_line (debug (count 10000000 0)) term
    Success
