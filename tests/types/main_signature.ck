# `main` is `fn main args sys -> code : args~List String, sys~System,
# code~ExitCode` (D31): types left out are those, others are errors.
module main_signature

import std.system (System)
import std.terminal

export fn main args sys -> code : sys~System
    let System { term } = sys
    terminal.print_line "hello" term
