# How `display` shows a duration: without units, in the largest of ns, µs,
# ms and s in which it is at least 1; with units, each unit in the list
# shows its part of the split, in the list's order.
module duration_display

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (display)
import std.time (Duration, Unit, millis, secs, Nanos, Micros, Millis, Seconds, Minutes, Hours)

fn show d us t : d~Duration, us~List Unit, t~Term
    terminal.print_line (display d us) t

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    show (Duration 0) [] t
    show (Duration 7) [] t
    show (Duration 1500) [] t
    show (millis 250) [] t
    show (Duration 1500000000) [] t
    show (Duration 1000000001) [] t
    show (secs 3600) [] t
    show (secs 63) [Minutes, Seconds, Minutes] t
    show (secs 63) [Seconds, Minutes] t
    show (millis 3500) [Hours, Minutes, Seconds] t
    show (millis 90250) [Minutes, Seconds] t
    show (millis 1500) [Millis] t
    show (millis 3723500) [Hours, Seconds] t
    show (Duration 0) [Seconds] t
    show (Duration 1234567) [Millis, Micros, Nanos] t
    show (millis 90000) [Minutes] t
    Success
