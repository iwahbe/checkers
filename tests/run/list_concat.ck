module list_concat

# `xs ++ ys` on lists shares `ys`: 100000 prepends finish at once. A copy of
# the right operand makes this program run for minutes.

import std.system (System, ExitCode)
import std.terminal

fn prepend n xs -> r : n~Nat, xs~List Nat, r~List Nat
    if n == 0 then xs else prepend (n - 1) ([0] ++ xs)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let tail = [3, 4]
    let joined = [1, 2] ++ tail
    terminal.print_line (format joined) sys.term
    terminal.print_line (format tail) sys.term
    terminal.print_line (format ([] ++ tail)) sys.term
    terminal.print_line (format (tail ++ [])) sys.term
    terminal.print_line (format (len (prepend 100000 tail))) sys.term
    Success
