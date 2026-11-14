# sort.ck — insertion sort, proven correct (SPEC §9.6, milestones M3, M23).
#
#   sort [3, 1, 2] == [1, 2, 3]
#   sort ["b", "a"] == ["a", "b"]
#
# The postcondition says the result is sorted and is a permutation of the
# input. It sorts any type with an order (`Ord a`, D136): comparing with
# `le`, and using one of the order's lemmas, `total`, where `x` doesn't come
# before `y`. Each recursive call may assume its own postcondition
# (induction, D50), and Z3 does the rest. `examples/resort.ck` uses this
# module through its exported postconditions and lemma only. (`std.list`
# has a merge sort.)

module sort

import std.list (sorted, perm)

# The first element, or `d` for an empty list.
fn first_or d xs -> r : d~a, xs~List a, r~a
    match xs
        []     -> d
        x :: _ -> x

# Insert `x` into a sorted list. The last postcondition says what the new
# first element is: the caller needs it to show its own result is sorted.
fn insert x ys -> zs : Ord a, x~a, ys~List a, sorted ys,
                       zs~List a, sorted zs, perm (x :: ys) zs,
                       first_or x zs == x or first_or x zs == first_or x ys
    match ys
        []        -> [x]
        y :: rest ->
            have total x y
            if le x y then x :: ys else y :: insert x rest

export fn sort xs -> ys : Ord a, xs~List a, ys~List a, sorted ys, perm xs ys
    match xs
        []        -> []
        x :: rest -> insert x (sort rest)

# Exported proofs (SPEC §6): importers can't see `sort`'s body, so the facts
# they need come from here. Sorting a sorted list changes nothing.
export lemma sort_of_sorted xs : Ord a, xs~List a, sorted xs
    ensures sort xs == xs
    proof
        match xs
            []        -> auto
            x :: rest -> have sort_of_sorted rest

check sort [3, 1, 2] == [1, 2, 3]
check sort [5, 5, -1, 0] == [-1, 0, 5, 5]
check sort ["pear", "apple", "fig"] == ["apple", "fig", "pear"]
