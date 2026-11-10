module counters

# 4 counters, each bumped 200 times by separate behaviours; the final
# `when` holds all four, so it runs after every bump scheduled before it
# (causal order, D66). Every schedule prints the same total.

import std.system (System, ExitCode)
import std.cown (Cown, Sched)
import std.future (Future)
import std.terminal (Term)

fn bump c k sched -> u : c~Cown Nat, k~Nat, sched~Sched, u~()
    decreasing k
    if k == 0
        ()
    else
        when n = c using sched
            n + 1
        bump c (k - 1) sched

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term, sched } = sys
    let a = cown.new 0 sched
    let b = cown.new 0 sched
    let c = cown.new 0 sched
    let d = cown.new 0 sched
    bump a 200 sched
    bump b 200 sched
    bump c 200 sched
    bump d 200 sched
    when w = a, x = b, y = c, z = d using sched
        terminal.print_line ("total " ++ format (w + x + y + z)) term
        (w, x, y, z)
    future.ready Success
