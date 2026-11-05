# terminal.ck — standard input, output and error.
module terminal

import files (IoError)

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
