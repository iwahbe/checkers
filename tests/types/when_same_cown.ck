module when_same_cown

# A `when` holds each of its cowns once: naming one cown twice is an error.

import std.cown (Cown, Sched)

fn twice c sched -> r : c~Cown Nat, sched~Sched, r~Unit
    when a = c, b = c using sched
        (a + 1, b + 1)
    ()
