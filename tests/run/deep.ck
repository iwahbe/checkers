module deep

# Non-tail recursion nests (big stack); tail recursion runs in constant space.

import std.system (System, ExitCode)
import std.terminal
import std.list (map, length)
import std.string (debug)

fn upto n -> xs : n~Nat, xs~List Nat
    decreasing n
    match n
        0 -> []
        _ -> n :: upto (n - 1)

fn count_down n acc -> r : n~Nat, acc~Nat, r~Nat
    decreasing n
    match n
        0 -> acc
        _ -> count_down (n - 1) (acc + 1)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (length (map (+ 1) (upto 100000)))) sys.term
    terminal.print_line (debug (count_down 1000000 0)) sys.term
    Success
