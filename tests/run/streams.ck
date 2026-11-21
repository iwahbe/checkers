# Standard input, output and error as files (D112): read a line, exactly n
# bytes, some bytes and the rest; handles share the streams' buffers with
# `print_line`, so output stays in order.
module streams

import std.system (System, ExitCode)
import std.terminal
import std.files
import std.string (debug)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    let input = terminal.stdin term
    let (header, input) = files.read_line input
    let (body, input) = files.read_exactly 5 input
    let (some, input) = files.read_some 3 input
    let (rest, input) = files.read_rest input
    let (tail, input) = files.read_rest input
    files.close input
    terminal.print_line (debug header) term
    terminal.print_line (debug body ++ " " ++ debug some ++ " " ++ debug rest ++ " " ++ debug tail) term
    let out = terminal.stdout term
    let (w, out) = files.write_bytes b"one, " out
    terminal.print_line "two" term
    let (_, out) = files.write_line "three" out
    files.close out
    let err = terminal.stderr term
    let (e, err) = files.write_bytes b"to stderr\n" err
    files.close err
    terminal.print_line (debug w ++ " " ++ debug e) term
    Success
