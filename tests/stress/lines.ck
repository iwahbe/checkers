module lines

# 40 behaviours on 40 different cowns each print one long line. They may
# come in any order, but a `terminal` call is atomic (D68): no line is ever
# split by another.

import system (System, ExitCode)
import cown (Cown, Sched)
import future (Future)
import terminal (Term)

fn rep k s -> r : k~Nat, s~String, r~String
    decreasing k
    if k == 0
        ""
    else
        s ++ rep (k - 1) s

fn shout term sched k -> u : term~Term, sched~Sched, k~Nat, u~()
    decreasing k
    if k == 0
        ()
    else
        let c = cown.new k sched
        when n = c using sched
            terminal.print_line ("line " ++ format n ++ " " ++ rep 200 "ab") term
            n
        shout term sched (k - 1)

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term, sched } = sys
    shout term sched 40
    future.ready Success
