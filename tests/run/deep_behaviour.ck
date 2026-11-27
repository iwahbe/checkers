# Deep non-tail recursion inside a behaviour (#607): each behaviour runs on a
# stack of its own, as deep as a worker's (#564, §13.8).
module deep_behaviour

import std.system (System, ExitCode)
import std.terminal
import std.list (map, length)
import std.future (Future)
import std.string (debug)

fn upto n -> xs : n~Nat, xs~List Nat
    decreasing n
    match n
        0 -> []
        _ -> n :: upto (n - 1)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, sched } = sys
    let r = future.fork sched $ \_ ->
        length (map (+ 1) (upto 1000000))
    terminal.print_line (debug (future.join r)) term
    Success
