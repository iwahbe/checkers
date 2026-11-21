module main_inferred

# `main`'s types, left out, are D31's.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

export fn main args sys -> code
    let System { term } = sys
    terminal.print_line (debug (len args)) term
    Success
