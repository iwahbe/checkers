# An array too large to allocate (#667, #25): the byte size of 2^62 `U32`s
# wraps around a machine word to 0.
module too_large_wraps

import std.system (System, ExitCode)
import std.terminal
import std.array
import std.string (debug)

fn low i -> r : i~Nat, r~U32
    7

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let xs = array.init 4611686018427387904 low
    terminal.print_line (debug (len xs)) sys.term
    Success
