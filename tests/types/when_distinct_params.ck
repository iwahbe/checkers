module when_distinct_params

# Two parameters may be the same cown: a `when` holding both needs them
# to differ, required of the caller with `x != y`.

import std.cown (Cown, Sched)

fn exchange x y sched -> r : x~Cown Nat, y~Cown Nat, sched~Sched, r~Unit
    when a = x, b = y using sched
        (b, a)
    ()

fn required x y sched -> r : x~Cown Nat, y~Cown Nat, x != y, sched~Sched, r~Unit
    when a = x, b = y using sched
        (b, a)
    ()

# Cowns of types that differ for every instantiation are different cowns.
fn other_types x y sched -> r : x~Cown Nat, y~Cown String, sched~Sched, r~Unit
    when a = x, b = y using sched
        (a, b)
    ()

fn other_shapes x y sched -> r : x~Cown (List a), y~Cown Nat, sched~Sched, r~Unit
    when a = x, b = y using sched
        (a, b)
    ()

# A `Cown a` may be a `Cown Nat`.
fn generic x y sched -> r : x~Cown a, y~Cown Nat, sched~Sched, r~Unit
    when a = x, b = y using sched
        (a, b)
    ()

fn three x y z sched -> r : x~Cown Nat, y~Cown Nat, z~Cown Nat, x != y, y != z, sched~Sched, r~Unit
    when a = x, b = y, c = z using sched
        (a, b, c)
    ()
