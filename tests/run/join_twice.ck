# A future joined twice gives both joins its value.
module join_twice

import std.system (System, ExitCode)
import std.future (Future)
import std.terminal

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term, sched } = sys
    let a = future.fork sched $ \_ ->
        "shared"
    let b = future.join a sched $ \x ->
        x ++ " once"
    let c = future.join a sched $ \y ->
        y ++ " twice"
    let d = future.join (future.both b c) sched $ \(p, q) ->
        terminal.print_line p term
        terminal.print_line q term
        Success
    d
