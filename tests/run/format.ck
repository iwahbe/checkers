module format

# `format` renders values as Checkers source (D42).

import std.system (System, ExitCode)
import std.terminal (Term)

record Point
    x~Int
    y~Int

enum Shape
    Rect w h : w~Nat, h~Nat

fn show_all term : term~Term
    terminal.print_line (format 42) term
    terminal.print_line (format (-7)) term
    terminal.print_line (format "a string") term
    terminal.print_line (format ["a", "b"]) term
    terminal.print_line (format [1, 2, 3]) term
    terminal.print_line (format (Point 1 (-2))) term
    terminal.print_line (format (Some (Rect 2 3))) term
    terminal.print_line (format (Ok True)) term
    terminal.print_line (format (1, "x", ())) term
    terminal.print_line (format b"hi\n") term
    terminal.print_line (format (None)) term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    show_all sys.term
    Success
