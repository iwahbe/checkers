module known_layout

# An array of values bounded by a value known at compile time is laid out as
# for the same bound written as a literal: `i % math.pow 2 8` is below 256,
# so the array is packed one byte per element and shows as bytes.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)
import std.array
import std.math

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (array.init 4 (\i -> i % math.pow 2 8))) sys.term
    terminal.print_line (debug (array.init 4 (\i -> i % 256))) sys.term
    Success
