module debug

# `debug` shows values as Checkers source: strings quoted at every level,
# the top included; functions as `<function>`.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)

record Point
    x~Int
    y~Int

enum Shape
    Rect w h : w~Nat, h~Nat

fn same x -> y : x~Int, y~Int
    x

fn show_all term : term~Term
    terminal.print_line (debug 42) term
    terminal.print_line (debug (-7)) term
    terminal.print_line (debug "a string") term
    terminal.print_line (debug ["a", "b"]) term
    terminal.print_line (debug [1, 2, 3]) term
    terminal.print_line (debug (Point 1 (-2))) term
    terminal.print_line (debug (Some (Rect 2 3))) term
    terminal.print_line (debug (Ok True)) term
    terminal.print_line (debug (1, "x", ())) term
    terminal.print_line (debug b"hi\n") term
    terminal.print_line (debug (None)) term
    terminal.print_line (debug same) term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    show_all sys.term
    Success
