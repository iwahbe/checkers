module effect_calls

# A call given a capability or a `Sched` is not a function of its
# arguments: two such calls may return different values, wherever they
# are written. What the callee promises of its result is known.

import std.terminal (Term)
import std.cown (Cown, Sched)

fn need x y -> r : x~a, y~a, x == y, r~Unit
    ()

fn named term -> r : term~Term, r~Unit
    let a = terminal.read_line term
    let b = terminal.read_line term
    need a b

fn nested sched -> r : sched~Sched, r~Unit
    need (cown.new 0 sched) (cown.new 0 sched)

# One call's value is itself.
fn once term -> r : term~Term, r~Unit
    let a = terminal.read_line term
    need a a

fn closure term -> r : term~Term, r~Unit
    let g = \_ -> terminal.read_line term
    need (g ()) (g ())

record Caps
    term~Term
    n~Nat

# A capability inside an argument.
fn read caps -> s : caps~Caps, s~Nat, s >= caps.n
    caps.n

fn inside term -> r : term~Term, r~Unit
    let caps = Caps term 3
    need (read caps) (read caps)

# The postcondition is known of each call.
fn promised term -> r : term~Term, r~Unit
    let caps = Caps term 3
    let s = read caps
    have s >= 3
    ()

# Pure calls are functions of their arguments.
fn double n -> m : n~Nat, m~Nat
    n + n

fn pure n -> r : n~Nat, r~Unit
    need (double n) (double n)
