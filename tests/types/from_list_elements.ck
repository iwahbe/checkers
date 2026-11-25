# Which elements `array.from_list` gives is known to proofs: the first
# is the list's head, the rest are the array of the list's tail. From
# that, by induction, element `n` of any list's array, and through
# `to_list` an array's list.
module from_list_elements

import std.array
import std.list

lemma one x : x~Nat
    ensures (array.from_list [x])[0] == x
    proof
        have array.from_list_cons x [] 0

lemma second x y z : x~Nat, y~Nat, z~Nat
    ensures (array.from_list [x, y, z])[1] == y
    proof
        have array.from_list_cons x [y, z] 1
        have array.from_list_cons y [z] 0

# Element `n` of a list's array, against a function on the list.
fn at xs n -> r : xs~List Nat, n~Nat, n < list.length xs, r~Nat
    match xs
        x :: rest -> if n == 0 then x else at rest (n - 1)

lemma at_from_list xs n : xs~List Nat, n~Nat, n < list.length xs
    ensures (array.from_list xs)[n] == at xs n
    proof
        match xs
            x :: rest ->
                have array.from_list_cons x rest n
                if n > 0 then have at_from_list rest (n - 1) else auto

# Element `n` past an array joined before a list's array.
lemma after pre xs n : pre~Array Nat, xs~List Nat, n~Nat, len pre <= n, n < len pre + list.length xs
    ensures (pre ++ array.from_list xs)[n] == at xs (n - len pre)
    proof
        have at_from_list xs (n - len pre)

# The other way: an array's list starts with its first element.
lemma to_list_head xs : xs~Array Nat, len xs > 0
    ensures list.head (array.to_list xs) == Some xs[0]
    proof
        have array.from_list_to_list xs
        match array.to_list xs
            y :: ys -> have array.from_list_cons y ys 0
