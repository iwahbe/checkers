module main_alias

# An alias without a predicate is no precondition of `main` (D181).

import std.system (System, ExitCode)

type Args = a~List String

export fn main args sys -> code : args~Args, sys~System, code~ExitCode
    Failure 5
