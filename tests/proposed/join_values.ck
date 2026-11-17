# D174–D176 (proposed): `join` gives the values of a future or a tuple of
# futures; the rest of the block runs once they are there.
module join_values

import std.future (Future)
import std.future
import std.system (System, ExitCode)
import std.terminal

fn sum xs -> n : xs~List Nat, n~Nat
    match xs
        []        -> 0
        x :: rest -> x + sum rest

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { sched, term } = sys
    let a = future.fork sched $ \_ ->
        sum [1, 2, 3]
    let b = future.fork sched (\_ -> "six")
    let c = future.ready 15
    # `ts` is inferred: Then Nat (Then String (Last Nat)) (D175).
    let (x, y, z) = future.join (a, b, c) sched
    terminal.print_line (format x ++ " is " ++ y) term
    let w = future.join a sched
    if x + z == 21 and w == 6 then Success else Failure 1

# Expected output:
# 6 is six
# (exit code 0)
