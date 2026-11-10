# A behaviour waiting for standard input doesn't hold its thread (D113): the
# reader is scheduled first, yet `ping` is printed while it waits, and the
# input it waits for is only written once `ping` has been seen.
module stdin_reader

import std.system (System, ExitCode)
import std.terminal (Term)
import std.cown (Cown, Sched)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, sched } = sys
    let a = cown.new 0 sched
    let b = cown.new 0 sched
    when x = a using sched
        match terminal.read_line term
            Some l -> terminal.print_line ("got " ++ l) term
            None   -> terminal.print_line "end of input" term
        x
    when y = b using sched
        terminal.print_line "ping" term
        y
    Success
