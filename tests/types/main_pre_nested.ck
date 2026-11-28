# An alias of a refinement is a refinement (E0366, #668).
module main_pre_nested

import std.system (System, ExitCode)

type Some = a~List String, a != []

type Named = a~Some

export fn main args sys -> code : args~Named, sys~System, code~ExitCode
    Success
