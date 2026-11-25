# A sleeping behaviour doesn't hold its thread: four behaviours each sleep
# for a second. Run on one thread, they finish together, about a second
# after they start, not four seconds, as they would one after another.
module sleepers

import std.system (System, ExitCode)
import std.terminal (Term)
import std.future
import std.time (now, since, sleep, secs)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, clock, sched } = sys
    let start = now clock
    let a = future.fork sched $ \_ ->
        sleep clock (secs 1)
    let b = future.fork sched $ \_ ->
        sleep clock (secs 1)
    let c = future.fork sched $ \_ ->
        sleep clock (secs 1)
    let d = future.fork sched $ \_ ->
        sleep clock (secs 1)
    let _ = future.join (a, b, c, d)
    let took = since (now clock) start
    terminal.print_line (if took < secs 1 then "woke early" else if took < secs 4 then "awake" else "slept in turn") term
    Success
