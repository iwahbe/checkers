module main

import std.system (System, ExitCode, Success)
import lib

# Reached from nothing.
fn dead_in_main n -> r : n~Nat, r~Nat
    n + 3

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    Success
