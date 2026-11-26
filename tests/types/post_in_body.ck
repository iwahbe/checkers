# A call's postcondition is known wherever the prover unfolds the body that
# holds it: a builtin's (`array.from_list`), and a function's of the program.
module post_in_body

import std.array

fn one x -> r : x~Nat, r~Array Nat
    array.from_list [x]

lemma through_one x : x~Nat
    ensures len (one x) == 1

fn pair x -> r : x~Nat, r~Array Nat, len r == 2
    array.from_list [x, x]

fn twice x -> r : x~Nat, r~Array Nat
    pair x

lemma through_twice x : x~Nat
    ensures len (twice x) == 2
