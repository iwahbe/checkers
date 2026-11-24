module debug_own

# A type's own `Debug` replaces the derived one wherever a value of it is
# shown: by `debug` at the type, through generic code that has no clause,
# and inside other values (in parentheses where it has a space).

import std.system (System, ExitCode)
import std.terminal
import std.string (Debug, debug)

record Secret
    code~Int

instance Debug Secret
    fn debug s
        "Secret <hidden>"

enum Tag
    Small
    Big n : n~Int

instance Debug Tag
    fn debug t
        match t
            Small -> "small"
            Big n -> "big " ++ Debug.debug n

fn shown x -> s : x~a, s~String
    debug x

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    terminal.print_line (debug (Secret 7)) t
    terminal.print_line (shown (Secret 7)) t
    terminal.print_line (shown [Some (Secret 1), None]) t
    terminal.print_line (shown (Small, Big 3)) t
    terminal.print_line (shown [Some Small, Some (Big 4)]) t
    Success

check shown (Some (Secret 1)) == "Some (Secret <hidden>)"
