# An array too large to allocate (D184, #25): a count that doesn't fit a
# machine word.
module too_large_count

import std.system (System, ExitCode)
import std.terminal
import std.array
import std.string (debug)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let xs = array.repeat 1000000000000000000000000000000 7
    terminal.print_line (debug (len xs)) sys.term
    Success
