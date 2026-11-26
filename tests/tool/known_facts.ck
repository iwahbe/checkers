module known_facts

# The value of a call known at compile time, given to the prover, is in the
# trust ledger as computed. The values of this module's own functions'
# calls aren't known while it is checked, so none is given (`steps 30` is
# proved by unfolding `steps`).

import std.array

fn under_count a -> r : a~Nat, a < array.count 7 (array.repeat 256 7), r~Nat
    a

fn caller -> r : r~Nat
    under_count 255

fn steps n -> r : n~Nat, r~Nat
    decreasing n
    if n == 0 then 0 else 1 + steps (n - 1)

fn under_steps a -> r : a~Nat, a < steps 30, r~Nat
    a

fn own_caller -> r : r~Nat
    under_steps 29
