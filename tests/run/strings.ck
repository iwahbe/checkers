module strings

import system (System, ExitCode)
import terminal
import string
import utf8
import char

fn shout c -> s : c~Char, s~String
    if c == '!' then "!!!" else string.from_char c

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    let s = string.from_chars [char.from_ascii 'h', char.from_scalar 0xE9, char.from_scalar 0x1F600]
    terminal.print_line s term
    terminal.print_line (format (len s)) term
    terminal.print_line (string.concat_map shout "hi!") term
    terminal.print_line (format (utf8.encode "é")) term
    terminal.print_line ("ab" ++ "cd") term
    terminal.print_line (format (b"ab" ++ b"cd")) term
    terminal.print_line (format ([1] ++ [2, 3])) term
    Success
