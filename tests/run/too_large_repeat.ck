# An array too large to allocate is the runtime's `out of memory` (D184, #25):
# 2^61 elements, where a Rust `Vec` panicked with `capacity overflow`.
module too_large_repeat

import std.system (System, ExitCode)
import std.terminal
import std.array

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let xs = array.repeat 2305843009213693952 7
    terminal.print_line (format (len xs)) sys.term
    Success
