module blackbox

# A value given through `blackbox` is not known when compiling: `blackbox
# 2 + 3` is added when the program runs, while `2 + 3` is computed when
# compiling.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)
import std.hint (blackbox)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (blackbox 2 + 3)) sys.term
    terminal.print_line (debug (2 + 3)) sys.term
    Success
