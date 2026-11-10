# terminal.ck — standard input, output and error.
module std.terminal

import std.files (IoError)

export abstract enum Term

export fn print_line s term -> r : s~String, term~Term, r~Unit
    __builtin

export fn eprint_line s term -> r : s~String, term~Term, r~Unit
    __builtin

export fn read_all term -> r : term~Term, r~Result Bytes IoError
    __builtin

export fn read_line term -> r : term~Term, r~Option String
    __builtin

export fn describe e -> s : e~IoError, s~String
    files.describe e

# Write to standard output without adding a newline.
export fn write s term -> r : s~String, term~Term, r~Unit
    __builtin

export fn write_bytes b term -> r : b~Bytes, term~Term, r~Unit
    __builtin
