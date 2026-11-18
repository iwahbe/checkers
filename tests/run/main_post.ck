module main_post

# A postcondition of `fn main` is allowed (D181).

import std.system (System, ExitCode)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode, code == Failure 4
    Failure 4
