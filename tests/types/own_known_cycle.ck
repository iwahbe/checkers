module own_known_cycle

# A value whose computation needs, through the functions it calls, the
# declaration being checked is not known: `outer` calls `inner`, whose body
# uses `LIMIT`, so `LIMIT` is checked before `inner`'s body and its value
# can't be computed then. That is no error, but `by_constant` must then prove
# its result a `Nat`, and the prover doesn't see `array.count`'s value.

import std.array

let LIMIT = outer 6

fn outer k -> r : k~Nat, r~Int
    inner k

fn inner k -> r : k~Nat, r~Int
    if k > 100 then LIMIT else array.count 7 (array.repeat k 7) - 2

fn by_constant k -> r : k~Int, r~Nat
    if k < 0 then LIMIT else 0
