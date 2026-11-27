module folded_closure

# A closure known when compiling, called with arguments known then, is
# computed then too: `by_two 3` is `5` in the program.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

fn adder n -> f : n~Int, f~(Int -> Int)
    \x -> x + n

let BY_TWO = adder 2

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (BY_TWO 3)) sys.term
    Success
