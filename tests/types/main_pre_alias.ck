# A parameter of `fn main` whose type is a refinement (E0366, #668).
module main_pre_alias

import std.system (System, ExitCode)

type Some = a~List String, a != []

export fn main args sys -> code : args~Some, sys~System, code~ExitCode
    Success
