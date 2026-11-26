module own_known

# A value computed by a function of the module being checked is known at
# compile time once that function is proved, as an imported function's is:
# `i % SIZE` and `i % size 256` are below 256, so each array is packed one
# byte per element and shows as bytes, as for `i % 256`. `size` calls a
# sealed function, so the prover sees only that it is a `Nat`: the divisor is
# tested before it is used.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)
import std.array

fn size k -> r : k~Nat, r~Nat
    array.count 7 (array.repeat k 7)

let SIZE = size 256

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let by_constant = \i -> if 0 < SIZE then i % SIZE else 0
    terminal.print_line (debug (array.init 4 by_constant)) sys.term
    let by_call = \i -> if 0 < size 256 then i % size 256 else 0
    terminal.print_line (debug (array.init 4 by_call)) sys.term
    terminal.print_line (debug (array.init 4 (\i -> i % 256))) sys.term
    Success
