module format_template

# `format` templates: named and positional holes, options, `{debug x}`,
# escaped braces, and a template with no holes.

import std.system (System, ExitCode)
import std.terminal
import std.string (format, debug, Hex, Quoted)

record Point
    x~Int
    y~Int

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    let name = "Ada"
    let age = 36
    terminal.print_line format"{name} is {age}" t
    terminal.print_line format"{age | Hex} {name | Quoted}" t
    terminal.print_line (format"{} and {| Hex}" "x" 255) t
    terminal.print_line format"{debug (Point 1 2)} {debug name}" t
    terminal.print_line (format"{}" (debug [1, 2])) t
    terminal.print_line format"{{{age + 1}}}" t
    terminal.print_line format"plain" t
    Success
