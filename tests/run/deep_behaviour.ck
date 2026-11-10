# Deep non-tail recursion inside a behaviour (D113): each behaviour runs on a
# stack of its own, as deep as a worker's (D75, §13.8).
module deep_behaviour

import std.system (System, ExitCode)
import std.terminal
import std.list (map, length)
import std.future (Future)

fn upto n -> xs : n~Nat, xs~List Nat
    decreasing n
    match n
        0 -> []
        _ -> n :: upto (n - 1)

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term, sched } = sys
    r <- fork using sched
        length (map (+ 1) (upto 1000000))
    done <- join n = r using sched
        terminal.print_line (format n) term
        Success
    done
