# A `let main` whose function has the wrong types (E0366, #668).
module main_let_wrong

import std.system (System, ExitCode)

fn go args sys -> code : args~Nat, sys~System, code~Nat
    args

export let main = go
