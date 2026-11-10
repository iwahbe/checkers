module behaviours

# Benchmark (M16, §13.7): a fork/join tree of 65 536 behaviours that each add
# two numbers. Run with `--threads 1` and `--threads 2`; compare before and
# after a scheduler change.

import std.system (System, ExitCode)
import std.cown (Sched)
import std.future (Future)
import std.terminal (Term)

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
    let t = sum 1 65536 sched
    done <- join s = t using sched
        terminal.print_line ("sum " ++ format s) term
        Success
    done
