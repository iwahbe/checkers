module tree

# A fork/join tree summing 1..1024: every leaf is a `fork`, every inner
# node a `join` of its two halves. The result does not depend on which
# worker runs what.

import system (System, ExitCode)
import cown (Sched)
import future (Future)
import terminal (Term)

fn sum lo n sched -> f : lo~Nat, n~Nat, sched~Sched, f~Future Nat
    decreasing n
    if n <= 1
        r <- fork using sched
            lo * n
        r
    else
        let h = n / 2
        let l = sum lo h sched
        let r = sum (lo + h) (n - h) sched
        s <- join x = l, y = r using sched
            x + y
        s

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term, sched } = sys
    let t = sum 1 1024 sched
    done <- join s = t using sched
        terminal.print_line ("sum " ++ format s) term
        Success
    done
