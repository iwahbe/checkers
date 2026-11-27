module known_own_call

# A lemma knows the value of a call of the module's own function known at
# compile time, though the prover can't see through its body: the body
# branches on a sealed function of another module.

import known.predicate

fn value x -> n : x~Nat, n~Nat
    if predicate.positive x then 1 else 0

export lemma by_value
    ensures value 1 == 1
