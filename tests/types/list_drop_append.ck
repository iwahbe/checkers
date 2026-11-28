# Dropping the front of an append, and the first element after a
# drop, follow from lemmas in `std.list` for any element type.
module list_drop_append

import std.list

lemma drop_after l r : l~List a, r~List a
    ensures list.drop (list.length l) (l ++ r) == r
    proof
        have list.drop_append l r

lemma drop_inside n l r : n~Nat, l~List a, r~List a, n <= list.length l
    ensures list.drop n (l ++ r) == list.drop n l ++ r
    proof
        have list.drop_append_within n l r

lemma head_after l y r : l~List a, y~a, r~List a
    ensures list.head (list.drop (list.length l) (l ++ (y :: r))) == Some y
    proof
        have list.drop_append l (y :: r)

lemma drop_has_head i xs : i~Nat, xs~List a, list.head (list.drop i xs) != None
    ensures i < list.length xs
    proof
        have list.head_drop i xs
