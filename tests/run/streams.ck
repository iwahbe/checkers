# Standard input, output and error as files (D112): read a line, exactly n
# bytes, some bytes and the rest; handles share the streams' buffers with
# `print_line`, so output stays in order.
module streams

import std.system (System, ExitCode)
import std.terminal
import std.files

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    let input = terminal.stdin term
    header <- files.read_line input
    body <- files.read_exactly 5 input
    some <- files.read_some 3 input
    rest <- files.read_rest input
    tail <- files.read_rest input
    files.close input
    terminal.print_line (format header) term
    terminal.print_line (format body ++ " " ++ format some ++ " " ++ format rest ++ " " ++ format tail) term
    let out = terminal.stdout term
    w <- files.write_bytes b"one, " out
    terminal.print_line "two" term
    _ <- files.write_line "three" out
    files.close out
    let err = terminal.stderr term
    e <- files.write_bytes b"to stderr\n" err
    files.close err
    terminal.print_line (format w ++ " " ++ format e) term
    Success
