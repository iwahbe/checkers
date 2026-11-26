module bad_exit

# An exit code proved only from an `admit` is checked when `main` returns
# it (§13.3).

import std.system (System, ExitCode)

lemma code n : n~Nat
    ensures n < 256
    proof
        admit

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    have code 300
    Failure 300
