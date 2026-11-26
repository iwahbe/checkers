module known_layout

# An array of values bounded by a value known at compile time is laid out as
# for the same bound written as a literal: `i % math.pow 2 8` is below 256,
# as is `i % array.count 7 (array.repeat 256 7)` (a sealed function's
# value), so each array is packed one byte per element and shows as bytes.
# The prover sees a sealed function's postconditions only, so the divisor is
# tested before it is used.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)
import std.array
import std.math

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (array.init 4 (\i -> i % math.pow 2 8))) sys.term
    let count = \i -> if 0 < array.count 7 (array.repeat 256 7) then i % array.count 7 (array.repeat 256 7) else 0
    terminal.print_line (debug (array.init 4 count)) sys.term
    terminal.print_line (debug (array.init 4 (\i -> i % 256))) sys.term
    Success
