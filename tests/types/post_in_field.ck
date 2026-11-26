# A call's postcondition is known wherever the prover unfolds the body that
# holds it, also when the call's result is a part of a value that a field
# read, a tuple's component, a `match` or a `let` takes out, and when the
# body is a constant's.
module post_in_field

import std.array

record Box
    xs~Array Nat
    n~Nat

fn empty -> b : b~Box
    Box (array.from_list []) 0

lemma by_field
    ensures len empty.xs == 0

record Outer
    inner~Box

fn nested -> o : o~Outer
    Outer (Box (array.from_list [1]) 0)

lemma by_nested_field
    ensures len nested.inner.xs == 1

fn pair -> p : p~(Array Nat, Nat)
    (array.from_list [1, 2], 0)

fn by_component -> n : n~Nat, n == 2
    let (xs, _) = pair
    len xs

enum Shape
    Full xs : xs~Array Nat
    Hollow

fn full -> s : s~Shape
    Full (array.from_list [1])

fn by_match -> n : n~Nat, n == 1
    match full
        Full xs -> len xs
        Hollow -> 1

fn by_let -> n : n~Nat, n == 0
    let b = empty
    len b.xs

fn single x -> b : x~Nat, b~Box
    Box (array.from_list [x]) x

lemma by_field_of_call x : x~Nat
    ensures len (single x).xs == 1
