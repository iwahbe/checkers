# terminal.ck — standard input, output and error.
module std.terminal

import std.files (IoError, File)

# The authority to use standard input, output and error; part of `System`.
export abstract enum Term

# Write `s` and a newline to standard output.
export fn print_line s term -> r : s~String, term~Term, r~Unit
    __builtin

# Write `s` and a newline to standard error.
export fn eprint_line s term -> r : s~String, term~Term, r~Unit
    __builtin

# Everything left on standard input.
export fn read_all term -> r : term~Term, r~Result Bytes IoError
    __builtin

# The next line of standard input, without its newline; `None` at the end.
export fn read_line term -> r : term~Term, r~Option String
    __builtin

# The error in words.
export fn describe e -> s : e~IoError, s~String
    files.describe e

# Write to standard output without adding a newline.
export fn write s term -> r : s~String, term~Term, r~Unit
    __builtin

# Write `b` to standard output.
export fn write_bytes b term -> r : b~Bytes, term~Term, r~Unit
    __builtin

# Standard input, output and error as files (D112). Each call gives a new
# handle; handles to one stream share its buffer with each other and with
# the functions above, and closing one closes the handle, not the stream.
export fn stdin term -> f : term~Term, f~File
    __builtin

# Standard output as a file (see `stdin`).
export fn stdout term -> f : term~Term, f~File
    __builtin

# Standard error as a file (see `stdin`).
export fn stderr term -> f : term~Term, f~File
    __builtin
