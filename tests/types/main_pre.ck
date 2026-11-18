# The runtime can't prove a precondition of `fn main` (E0366, D181).
module main_pre

import std.system (System, ExitCode)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode, args != []
    Success
