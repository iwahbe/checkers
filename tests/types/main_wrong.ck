# A `main` whose written types aren't #517's (E0366).
module main_wrong

import std.system (System, ExitCode)

export fn main args sys -> code : args, sys~System, code~Nat
    0
