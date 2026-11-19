module forall_counterexample

# A counterexample satisfies every fact in scope, a `forall` too, though the
# prover uses a `forall` only by name.

# Z3's first model breaks `same` (`a[0] != b[0]`): no counterexample.
lemma by_index a b : a~Bytes, b~Bytes, len a == len b, same: forall k : k~Nat, k < len a, a[k] == b[k]
    ensures a == b

# Every model breaks `zero`: no counterexample, and `have zero x` proves it.
lemma by_function f x : f~(Int -> Int), x~Int, zero: forall k : k~Int, f k == 0
    ensures f x == 0

# A real counterexample keeps `small`.
lemma kept x : x~Nat, small: forall k : k~Nat, k < x, k < 5
    ensures x < 3
