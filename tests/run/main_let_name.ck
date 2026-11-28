module main_let_name

# `let main` names a function: neither is unused, and `main` keeps its name
# (#668).

import std.system (System, ExitCode)
import std.terminal

fn go args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line "ran" sys.term
    Success

export let main = go
