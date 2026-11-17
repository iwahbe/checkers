# D176 (c) (proposed): a `when` body gives the cowns' new values now, so it
# can't wait for a future.
module join_in_when

import std.future (Future)
import std.future
import std.cown (Cown, Sched)
import std.cown

fn add_later c f sched -> u : c~Cown Nat, f~Future Nat, sched~Sched, u~Unit
    when n = c using sched
        let k = future.join f sched
        n + k
    ()

# Expected:
# error[E0201]: type mismatch: expected `Nat`, found `Future Nat`
#   --> join_in_when.ck:13:5
#    |
# 13 |     when n = c using sched
#    |     ^^^^ this `when` body's value is a `Future Nat`
#    = note: the `join` on line 14 runs the rest of the body later, but a `when` body gives the cowns' new values now
