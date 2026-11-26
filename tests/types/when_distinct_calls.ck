module when_distinct_calls

# A cown a call returns differs from every cown in scope that the call
# can't reach.

import std.cown (Cown, Sched)
import std.list (contains, unique)

fn exchange x y sched -> r : x~Cown Nat, y~Cown Nat, x != y, sched~Sched, r~Unit
    when a = x, b = y using sched
        (b, a)
    ()

fn same c sched -> r : c~Cown Nat, sched~Sched, r~Unit
    exchange c c sched

fn fresh_pair sched -> r : sched~Sched, r~Unit
    let c = cown.new 0 sched
    let d = cown.new 0 sched
    exchange c d sched

fn pick c sched -> r : c~Cown Nat, sched~Sched, r~Cown Nat
    c

fn make sched -> r : sched~Sched, r~Cown Nat
    cown.new 0 sched

fn both c sched -> r : c~Cown Nat, sched~Sched, r~Unit
    let d = make sched
    exchange c d sched
    let e = pick c sched
    exchange c e sched

# A closure that captured `c` can return it.
fn closure c sched -> r : c~Cown Nat, sched~Sched, r~Unit
    let g = \_ -> c
    let d = g ()
    exchange c d sched

# What a postcondition promises is known.
fn other c sched -> r : c~Cown Nat, sched~Sched, r~Cown Nat, r != c
    cown.new 0 sched

fn promised c sched -> r : c~Cown Nat, sched~Sched, r~Unit
    let d = other c sched
    exchange c d sched

# A call written anywhere, not only named by `let`.
fn nested c sched -> r : c~Cown Nat, sched~Sched, r~Unit
    exchange c (make sched) sched

# Cowns inside a call's result are new too.
fn make_two sched -> r : sched~Sched, r~(Cown Nat, Cown Nat)
    (cown.new 0 sched, cown.new 1 sched)

fn parts c sched -> r : c~Cown Nat, sched~Sched, r~Unit
    let (d, e) = make_two sched
    exchange c d sched
    exchange d e sched              # `make_two` may return one cown twice

# A list's elements: new cowns differ from all of them.
fn listed cs sched -> r : cs~List (Cown Nat), sched~Sched, r~Unit
    match cs
        x :: _ ->
            let d = cown.new 0 sched
            exchange x d sched
        []     -> ()

fn outside d cs -> r : d~Cown Nat, cs~List (Cown Nat), not (contains cs d), r~Unit
    ()

fn not_listed cs sched -> r : cs~List (Cown Nat), sched~Sched, r~Unit
    let d = cown.new 0 sched
    outside d cs

# Distinct elements, by the list's own condition.
fn first_two cs sched -> r : cs~List (Cown Nat), unique cs, sched~Sched, r~Unit
    match cs
        x :: y :: _ -> exchange x y sched
        _           -> ()
