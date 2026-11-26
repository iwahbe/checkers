# Which elements `list.take` and `list.drop` give is known to proofs
# outside `std`: their bodies are visible.
module list_take_drop_elements

import std.list

lemma drop_none xs : xs~List Int
    ensures list.drop 0 xs == xs

lemma drop_past_first x xs : x~Int, xs~List Int
    ensures list.drop 1 (x :: xs) == xs

lemma take_none xs : xs~List Int
    ensures list.take 0 xs == []

lemma take_first x xs : x~Int, xs~List Int
    ensures list.take 1 (x :: xs) == [x]

lemma head_of_drop k : k~Nat, k < 3
    ensures list.head (list.drop k [10, 20, 30]) == Some (10 + 10 * k)
