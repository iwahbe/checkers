# An array too large to allocate (D184, #25): 2^60 strings are 2^63 bytes,
# more than an allocation can be.
module too_large_words

import std.system (System, ExitCode)
import std.terminal
import std.array
import std.string (debug)

fn name i -> r : i~Nat, r~String
    debug i

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let xs = array.init 1152921504606846976 name
    terminal.print_line (debug (len xs)) sys.term
    Success
