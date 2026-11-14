module main_inferred

# `main`'s types, left out, are D31's.

import std.system (System, ExitCode)
import std.terminal

export fn main args sys -> code
    let System { term } = sys
    terminal.print_line (format (len args)) term
    Success
