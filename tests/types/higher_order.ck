module higher_order

# The prover specializes a function that takes a function argument when the
# argument is known: a top-level function or a lambda without free variables.

import list (map, length)

fn double x -> y : x~Int, y~Int
    2 * x

fn first_or_zero xs -> r : xs~List Int, r~Int
    match xs
        []     -> 0
        x :: _ -> x

fn doubled xs -> r : xs~List Int, r~Bool, r
    first_or_zero (map double xs) == 2 * first_or_zero xs

fn lam xs -> r : xs~List Int, r~Bool, r
    first_or_zero (map (\x -> x + 1) [1, 2]) == 2

lemma kept xs : xs~List Int
    ensures length (map double xs) == length xs
    proof
        match xs
            []        -> auto
            _ :: rest -> have kept rest

fn wrong xs -> r : xs~List Int, r~Bool, r
    first_or_zero (map double xs) == first_or_zero xs
