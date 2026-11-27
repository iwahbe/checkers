# `list.any` calls its predicate only with elements of the list, and is
# `list.all` negated.
module list_any

import std.list

fn past xs n x -> r : xs~List Int, n~Int, x~Int, list.contains xs x, r~Bool
    x > n

fn some_past n xs -> r : n~Int, xs~List Int, r~Bool
    list.any (past xs n) xs

lemma not_all_below n xs : n~Int, xs~List Int, not (list.all (\x -> x <= n) xs)
    ensures list.any (\x -> x > n) xs
    proof
        have list.any_all (\x -> x > n) xs

check some_past 2 [1, 2, 3]
check not (some_past 3 [1, 2, 3])
check not (list.any (\x -> x > 0) [])
