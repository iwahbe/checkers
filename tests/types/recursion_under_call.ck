# A `decreasing` function whose recursion is under a `match` on another
# recursive function's result, passing a parameter unchanged, is unfolded
# as the search decides that `match`: a goal that needs it unfolded twice is
# proved, not given up on.
module recursion_under_call

import std.list

fn above k xs -> r : k~Nat, xs~List Int, r~List Int
    match xs
        []        -> []
        x :: rest -> if x > k then x :: above k rest else above k rest

fn below k xs -> r : k~Nat, xs~List Int, r~List Int
    match xs
        []        -> []
        x :: rest -> if x > k then below k rest else x :: below k rest

lemma split_length k xs : k~Nat, xs~List Int
    ensures list.length (above k xs) + list.length (below k xs) == list.length xs
    proof
        match xs
            []        -> auto
            _ :: rest -> have split_length k rest

fn rounds k got xs -> r : k~Nat, got~List Int, xs~List Int, r~List Int
    decreasing list.length xs
    have split_length k xs
    match above k xs
        []        -> got
        _ :: more ->
            have list.length (above k xs) == 1 + list.length more
            rounds k (got ++ above k xs) (below k xs)

lemma two_rounds k x y : k~Nat, x~Int, y~Int
    ensures rounds k [] [x, y] == above k [x, y]
