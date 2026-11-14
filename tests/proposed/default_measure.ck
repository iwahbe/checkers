# D150 (proposed): with no `decreasing`, a function recursing on a `Nat`
# that doesn't get structurally smaller is measured by its `Nat`
# parameters. Expected: no diagnostics; `fib 6 == 13` holds.
module default_measure

fn fib x -> n : x~Nat
    if x == 0 or x == 1 then 1 else fib (x - 1) + fib (x - 2)

check fib 6 == 13

# Any integer the facts show is `>= 0`, refined or not.
fn halves x -> n : x~Nat, x % 2 == 0
    if x == 0 then 0 else halves (x - 2) + 1

# A guard's distance: up to a bound.
fn count_from i n -> r : i~Nat, n~Nat
    if i < n then count_from (i + 1) n + 1 else 0

# A guard's distance: negative numbers rising to zero.
fn up x -> n : x~Int
    if x < 0 then up (x + 1) + 1 else 0

check halves 6 == 3
check count_from 2 5 == 3
check up (-3) == 3
