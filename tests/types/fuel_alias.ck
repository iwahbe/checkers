module fuel_alias

# Found: after a long computation in a condition (out of evaluation fuel),
# `Failure 1` was rejected: "a number literal needs numbers, but this is
# `U8`". Expected: no error. Unfolding a type alias costs no fuel.

import system (System, ExitCode)

fn sum_to n acc -> r : n~Nat, acc~Nat, r~Nat
    decreasing n
    if n == 0
        acc
    else
        sum_to (n - 1) (acc + n)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    if sum_to 3000000 0 == 4500001500000 then Success else Failure 1
