# A count or position that doesn't fit a machine word (D185): `read_exactly`
# gives fewer bytes only at the end, `read_some` at most that many, and no byte
# string has such a position.
module too_large_read

import std.system (System, ExitCode)
import std.terminal
import std.files
import std.bytes
import std.string (debug)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    let input = terminal.stdin term
    let (some, input) = files.read_some 1000000000000000000000000000000 input
    let (rest, input) = files.read_exactly 1000000000000000000000000000000 input
    let _ = files.close input
    let found = bytes.matches_at b"abc" 1000000000000000000000000000000 b""
    terminal.print_line (debug some ++ " " ++ debug rest ++ " " ++ debug found) term
    Success
