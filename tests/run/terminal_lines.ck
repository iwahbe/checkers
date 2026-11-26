module terminal_lines

# `terminal.read_line` gives each line's bytes as they are, without the
# `\n`, and `None` at the end of input.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.files
import std.string (debug)

partial fn lines term : term~Term
    match terminal.read_line term
        Ok (Some l) ->
            terminal.print_line (debug l) term
            lines term
        Ok None     -> terminal.print_line "the end" term
        Err e       -> terminal.print_line ("read failed: " ++ files.describe e) term

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    lines sys.term
    Success
