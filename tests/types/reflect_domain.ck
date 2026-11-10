# A definition recursing by `decreasing` is given to Z3 only where its
# recursion ends (D118): `half` ends where `x >= 1`, so outside that its
# value is unknown. A program with one wrong call is reported at once
# (it used to send Z3 unfolding `half 0` for minutes).
module reflect_domain

fn half x -> r : x~Nat, x >= 1, r~Nat
    decreasing x
    if x == 1 then 0 else 1 + half (x / 2)

# Inside its domain the definition unfolds as before.
lemma half_eight
    ensures half 8 == 3
    proof
        auto

# E0450 twice: the call's precondition, and the postcondition, which needs
# a value `half 0` doesn't have.
fn bad n -> r : n~Nat, r~Nat, r > 0
    let x = half 0
    x + 1

# Recursion that ends whatever the preconditions (the measure falls on every
# call): unguarded, so proofs about it don't have to establish them.
fn interleave l r -> out : l~List Nat, r~List Nat, out~List Nat, len out == len l + len r
    decreasing len l + len r
    match l
        []        -> r
        x :: rest -> x :: interleave r rest
