# A duration's rest in minutes or hours that no decimal writes exactly is
# cut off where a nanosecond is still more than the last place: 11 places
# for minutes, 13 for hours. Expected output:
#
#     1.66666666666m
#     0.0002777777777h
#     1m40s
module duration_inexact

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (display)
import std.time (secs, Minutes, Seconds, Hours)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (display (secs 100) [Minutes]) sys.term
    terminal.print_line (display (secs 1) [Hours]) sys.term
    terminal.print_line (display (secs 100) [Minutes, Seconds]) sys.term
    Success
