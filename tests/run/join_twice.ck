# A future joined twice gives both joins its value.
module join_twice

import std.system (System, ExitCode)
import std.future (Future)
import std.terminal

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term, sched } = sys
    a <- fork using sched
        "shared"
    b <- join x = a using sched
        x ++ " once"
    c <- join y = a using sched
        y ++ " twice"
    d <- join p = b, q = c using sched
        terminal.print_line p term
        terminal.print_line q term
        Success
    d
