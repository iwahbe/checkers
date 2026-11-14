# A lemma may conclude a `forall` (D146).
module forall_ensures

import std.list (sorted_by, sort_by, perm, length)

# Proved at fresh `x` and `y`, which the proof names.
lemma total_by key : Ord k, key~(a -> k)
    ensures forall x y : x~a, y~a, le (key x) (key y) or le (key y) (key x)
    proof
        have total (key x) (key y)

# `have total_by key` passes it on to `sort_by`'s `total`.
fn sort_keys key xs -> r : Ord k, key~(a -> k), xs~List a, r~List a, perm xs r
    have total_by key
    sort_by (\x y -> le (key x) (key y)) xs

# Its variables filled in, it is a fact about those values.
lemma pair key p q : Ord k, key~(a -> k), p~a, q~a
    ensures le (key p) (key q) or le (key q) (key p)
    proof
        have total_by key p q

# Premises are facts in the proof.
lemma above n : n~Int, n > 0
    ensures forall m : m~Int, m > n, m > 0

# Not true of every `m`.
lemma wrong
    ensures forall m : m~Int, m > 0

# A `forall` the caller would have to prove an `exists` from.
lemma negative
    ensures not (forall m : m~Int, m > 0)
