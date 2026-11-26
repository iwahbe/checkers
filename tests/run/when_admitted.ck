module when_admitted

# A `when` whose cowns are distinct only by an `admit` is checked when it
# is scheduled: naming one cown twice stops the program.

import std.system (System, ExitCode)
import std.cown (Cown, Sched)

lemma differ x y : x~Cown Nat, y~Cown Nat
    ensures x != y
    proof
        admit

fn twice c sched -> r : c~Cown Nat, sched~Sched, r~Unit
    have differ c c
    when a = c, b = c using sched
        (a + 1, b + 1)
    ()

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { sched } = sys
    let c = cown.new 0 sched
    twice c sched
    Success
