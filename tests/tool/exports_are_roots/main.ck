module main

import std.system (System, ExitCode, Success, Failure)
import lib

# Used by no module of the package: still part of its interface.
export fn also_offered n -> r : n~Nat, r~Nat
    n + 3

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    if lib.used 1 == 2 then Success else Failure 1
