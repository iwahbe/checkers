module when_last

import std.cown (Cown, Sched)

export fn bump c sched -> result : c~Cown Nat, sched~Sched, result~Unit
    when v = c using sched
        v + 1

export fn conditional c sched enabled -> result : c~Cown Nat, sched~Sched, enabled~Bool, result~Unit
    if enabled
        when v = c using sched
            v + 1
    else
        ()
