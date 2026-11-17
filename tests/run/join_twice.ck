# A future joined twice gives both joins its value.
module join_twice

import std.system (System, ExitCode)
import std.future (Future)
import std.terminal

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, sched } = sys
    let a = future.fork sched $ \_ ->
        "shared"
    let b = future.fork sched $ \_ ->
        future.join a ++ " once"
    let c = future.fork sched $ \_ ->
        future.join a ++ " twice"
    let (p, q) = future.join (b, c)
    terminal.print_line p term
    terminal.print_line q term
    Success
