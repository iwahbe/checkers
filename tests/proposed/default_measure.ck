# D150 (proposed): with no `decreasing`, a function recursing on a `Nat`
# that doesn't get structurally smaller is measured by its `Nat`
# parameters. Expected: no diagnostics; `fib 6 == 13` holds.
module default_measure

fn fib x -> n : x~Nat
    if x == 0 or x == 1 then 1 else fib (x - 1) + fib (x - 2)

check fib 6 == 13
