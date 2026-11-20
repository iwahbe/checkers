module forall_counterexample

# A counterexample satisfies every fact in scope, a `forall` too, though the
# prover uses a `forall` only by name.

# Every model breaks `zero`: no counterexample, and `have zero x` proves it.
lemma by_function f x : f~(Int -> Int), x~Int, zero: forall k : k~Int, f k == 0
    ensures f x == 0

# A real counterexample keeps `small`.
lemma kept x : x~Nat, small: forall k : k~Nat, k < x, k < 5
    ensures x < 3

# A `forall` over a refinement holds only where the refinement does: a real
# counterexample keeps `low`, with `x` outside it.
lemma refined f x : f~(Int -> Int), x~Int, low: forall k : k~(k~Int, k < 2), f k == 0
    ensures f x == 0
