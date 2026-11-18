# A byte count that doesn't fit a machine word (D185, proposed) reads what there
# is: `read_exactly` gives fewer bytes only at the end, `read_some` at most
# that many.
module too_large_read

import std.system (System, ExitCode)
import std.terminal
import std.files

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    let input = terminal.stdin term
    let (some, input) = files.read_some 1000000000000000000000000000000 input
    let (rest, input) = files.read_exactly 1000000000000000000000000000000 input
    files.close input
    terminal.print_line (format some ++ " " ++ format rest) term
    Success
