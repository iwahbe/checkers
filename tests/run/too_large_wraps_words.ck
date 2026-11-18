# An array too large to allocate (D184, #25): the byte size of 2^61 strings
# wraps around a machine word to 0.
module too_large_wraps_words

import std.system (System, ExitCode)
import std.terminal
import std.array

fn name i -> r : i~Nat, r~String
    format i

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let xs = array.init 2305843009213693952 name
    terminal.print_line (format (len xs)) sys.term
    Success
