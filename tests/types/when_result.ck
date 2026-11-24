module when_result

import std.cown (Cown, Sched)

export fn wrong c sched -> result : c~Cown Nat, sched~Sched, result~Nat
    when v = c using sched
        v + 1
