module display_options

# The standard library's `Display` options, alone and combined; where two
# conflict, the later one wins.

import std.system (System, ExitCode)
import std.terminal
import std.string (display, Hex, Binary, Octal, Plus, Digits, Quoted, Take)
import std.decimal (Places)
import std.decimal

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    let n = 255
    let m = -42
    terminal.print_line (display n []) t
    terminal.print_line (display n [Hex]) t
    terminal.print_line (display n [Binary]) t
    terminal.print_line (display n [Octal]) t
    terminal.print_line (display n [Plus]) t
    terminal.print_line (display n [Digits 5]) t
    terminal.print_line (display n [Hex, Digits 4, Plus]) t
    terminal.print_line (display m [Hex, Digits 4]) t
    terminal.print_line (display m [Plus]) t
    terminal.print_line (display 0 [Plus]) t
    terminal.print_line (display n [Hex, Binary]) t
    terminal.print_line (display n [Digits 8, Digits 2]) t
    let s = "naïve \"quote\"\n"
    terminal.print_line (display s []) t
    terminal.print_line (display s [Quoted]) t
    terminal.print_line (display s [Take 3]) t
    terminal.print_line (display s [Take 3, Quoted]) t
    terminal.print_line (display s [Take 100, Take 2]) t
    let d = decimal.of_int 1234
    terminal.print_line (display d []) t
    terminal.print_line (display d [decimal.Plus]) t
    terminal.print_line (display d [Places 2]) t
    terminal.print_line (display (decimal.of_int (-7)) [Places 1, decimal.Plus]) t
    terminal.print_line (display d [Places 3, Places 0]) t
    terminal.print_line (display True [] ++ " " ++ display False []) t
    Success
