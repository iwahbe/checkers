module std_specialized

# A standard library function called with a value known when compiling is
# specialized on it: `take 2` gets a copy taking only the list. Called
# with every argument known, it is computed when compiling.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)
import std.list

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (list.take 2 args)) sys.term
    terminal.print_line (debug (list.length [1, 2, 3])) sys.term
    Success
