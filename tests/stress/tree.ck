module tree

# A fork/join tree summing 1..1024: every leaf is a `fork`, every inner
# node a `fork` that joins its two halves. The result does not depend on which
# worker runs what.

import std.system (System, ExitCode)
import std.cown (Sched)
import std.future (Future)
import std.terminal (Term)
import std.string (debug)

fn sum lo n sched -> f : lo~Nat, n~Nat, sched~Sched, f~Future Nat
    decreasing n
    if n <= 1
        let r = future.fork sched $ \_ ->
            lo * n
        r
    else
        let h = n / 2
        let l = sum lo h sched
        let r = sum (lo + h) (n - h) sched
        future.fork sched $ \_ ->
            let (x, y) = future.join (l, r)
            x + y

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, sched } = sys
    let s = future.join (sum 1 1024 sched)
    terminal.print_line ("sum " ++ debug s) term
    Success
