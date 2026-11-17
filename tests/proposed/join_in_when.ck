# D176 (c) (proposed): a `when` body may join. It is parked, keeping its
# cown, until the future is filled; whatever fills a future never waits for
# a cown, so this can't deadlock.
module join_in_when

import std.future (Future)
import std.future
import std.cown (Cown, Sched)
import std.cown

fn add_later c f sched -> u : c~Cown Nat, f~Future Nat, sched~Sched, u~Unit
    when n = c using sched
        n + future.join f
    ()

# Expected: 0 errors.
