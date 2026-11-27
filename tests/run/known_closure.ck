module known_closure

# A lambda's closure known at compile time is static data, holding the values
# it captured: `adder 2` is computed when compiling, with `m` as 4, and
# nothing is built when the program runs.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)
import std.hint (blackbox)

fn adder n -> f : n~Int, f~(Int -> Int)
    let m = n * n
    \x -> x + m

let BY_TWO = adder 2

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (BY_TWO (blackbox 3))) sys.term
    Success
