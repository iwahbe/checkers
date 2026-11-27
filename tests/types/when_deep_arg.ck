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
