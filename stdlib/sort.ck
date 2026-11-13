# sort.ck — sorting lists (D138): stable merge sorts, in O(n log n)
# comparisons, each proved to give a sorted permutation of its input.
module std.sort

import std.bag
import std.list (length, take, drop, take_drop, bag_append, append_nil, perm_middle, head, perm, sorted, sorted_as, sorted_by)

# `xs` in order (`Ord`).
export fn sort xs -> r : Ord a, xs~List a, r~List a, sorted r, perm xs r, length r == length xs
    decreasing length xs
    match xs
        _ :: _ :: rest ->
            have length xs == 2 + length rest
            let k = length xs / 2
            let front = take k xs
            let back = drop k xs
            have take_drop k xs
            have bag_append front back
            let a = sort front
            let b = sort back
            have bag_append a b
            merge a b
        _              -> xs

fn merge xs ys -> r : Ord a, xs~List a, ys~List a, sorted xs, sorted ys,
                      r~List a, sorted r, perm (xs ++ ys) r, head r == head xs or head r == head ys,
                      length r == length xs + length ys
    decreasing length xs + length ys
    match xs
        []      -> ys
        x :: xr ->
            match ys
                []      ->
                    have append_nil xs
                    xs
                y :: yr ->
                    have total x y
                    if le x y
                        x :: merge xr ys
                    else
                        have perm_middle xs y yr
                        y :: merge xs yr

# `xs` in the order of `key` of each element (`Ord`): `sort_as (\p -> p.age)`.
export fn sort_as key xs -> r : Ord k, key~(a -> k), xs~List a, r~List a, sorted_as key r, perm xs r, length r == length xs
    decreasing length xs
    match xs
        _ :: _ :: rest ->
            have length xs == 2 + length rest
            let k = length xs / 2
            let front = take k xs
            let back = drop k xs
            have take_drop k xs
            have bag_append front back
            let a = sort_as key front
            let b = sort_as key back
            have bag_append a b
            merge_as key a b
        _              -> xs

fn merge_as key xs ys -> r : Ord k, key~(a -> k), xs~List a, ys~List a, sorted_as key xs, sorted_as key ys,
                             r~List a, sorted_as key r, perm (xs ++ ys) r, head r == head xs or head r == head ys,
                             length r == length xs + length ys
    decreasing length xs + length ys
    match xs
        []      -> ys
        x :: xr ->
            match ys
                []      ->
                    have append_nil xs
                    xs
                y :: yr ->
                    have total (key x) (key y)
                    if le (key x) (key y)
                        x :: merge_as key xr ys
                    else
                        have perm_middle xs y yr
                        y :: merge_as key xs yr

# `xs` in the order `le` gives, which must put any two elements in order
# one way or the other (`total`).
export fn sort_by le xs -> r : le~(a -> a -> Bool), xs~List a,
                               total: forall x y : x~a, y~a, le x y or le y x,
                               r~List a, sorted_by le r, perm xs r, length r == length xs
    decreasing length xs
    match xs
        _ :: _ :: rest ->
            have length xs == 2 + length rest
            let k = length xs / 2
            let front = take k xs
            let back = drop k xs
            have take_drop k xs
            have bag_append front back
            let a = sort_by le front
            let b = sort_by le back
            have bag_append a b
            merge_by le a b
        _              -> xs

fn merge_by le xs ys -> r : le~(a -> a -> Bool), xs~List a, ys~List a, sorted_by le xs, sorted_by le ys,
                            total: forall x y : x~a, y~a, le x y or le y x,
                            r~List a, sorted_by le r, perm (xs ++ ys) r, head r == head xs or head r == head ys,
                            length r == length xs + length ys
    decreasing length xs + length ys
    match xs
        []      -> ys
        x :: xr ->
            match ys
                []      ->
                    have append_nil xs
                    xs
                y :: yr ->
                    have total x y
                    if le x y
                        x :: merge_by le xr ys
                    else
                        have perm_middle xs y yr
                        y :: merge_by le xs yr

check sort [3, 1, 2, 2] == [1, 2, 2, 3]
check sort ["pear", "apple", "fig"] == ["apple", "fig", "pear"]
check sort_as (\x -> x * x) [-3, 2, 1] == [1, 2, -3]
check sort_by (\x y -> x >= y) [1, 3, 2] == [3, 2, 1]
