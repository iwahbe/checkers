# Writing to standard input is a runtime error with a plain message.
module streams_misuse

import std.system (System, ExitCode)
import std.terminal
import std.files

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    let input = terminal.stdin term
    r <- files.write_bytes b"x" input
    terminal.print_line (format r) term
    _ <- files.write_line "x" input
    files.close input
    Success
