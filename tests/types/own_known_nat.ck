module own_known_nat

# A value computed by a function of the module being checked is known at
# compile time once that function is proved: a non-negative one is a `Nat` by
# construction, with nothing to prove, as a literal is. The body of `shifted`
# calls a sealed function, so neither the type checker's evaluation nor the
# prover sees its value; it is computed by running it.

import std.array

fn shifted k -> r : k~Nat, r~Int
    array.count 7 (array.repeat k 7) - 2

let SHIFTED = shifted 6

fn by_constant k -> r : k~Int, r~Nat
    if k < 0 then SHIFTED else 0

fn by_call k -> r : k~Int, r~Nat
    if k < 0 then shifted 6 else 0
