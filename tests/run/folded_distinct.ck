module folded_distinct

# Two calls computed when compiling that differ only in a constructor
# without fields each have their own value: one `False`, one `True`.

import std.system (System, ExitCode)
import std.string (debug)
import std.terminal (Term)
import std.list

enum Tag
    Left
    Right

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (list.contains [Right] Left)) sys.term
    terminal.print_line (debug (list.contains [Right] Right)) sys.term
    Success
