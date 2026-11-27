module when_deep_arg

# A call given no cown, only a value of a type 40 `Option`s deep that
# holds none, returns a cown different from every cown in scope.

import std.cown (Cown, Sched)

fn exchange x y sched -> r : x~Cown Nat, y~Cown Nat, x != y, sched~Sched, r~Unit
    when a = x, b = y using sched
        (b, a)
    ()

fn make x sched -> r : x~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option Int))))))))))))))))))))))))))))))))))))))), sched~Sched, r~Cown Nat
    cown.new 0 sched

fn fresh c sched -> r : c~Cown Nat, sched~Sched, r~Unit
    let d = make None sched
    exchange c d sched

# A cown in scope inside records five deep differs from a new one.
record R1
    c~Cown Nat

record R2
    r~R1

record R3
    r~R2

record R4
    r~R3

record R5
    r~R4

fn inside w sched -> r : w~R5, sched~Sched, r~Unit
    let d = cown.new 0 sched
    exchange w.r.r.r.r.c d sched
