module bad_exit

import std.system (System, ExitCode)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    Failure 300
