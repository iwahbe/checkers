# The runtime can't prove a precondition of `main` (E0366, D181).
module main_let_pre

import std.system (System, ExitCode)

fn go args sys -> code : args~List String, sys~System, code~ExitCode, args != []
    Success

export let main = go
