module uncovered

# A `match` without the cases that can't occur (D144) runs as any other.

import std.system (System, ExitCode)
import std.terminal

fn head xs -> r : xs~List Int, xs != [], r~Int
    match xs
        x :: _ -> x

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (format (head [7, 8])) sys.term
    Success
