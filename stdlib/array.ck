# array.ck — functions on arrays (D133). `Array a` is in the prelude, with
# `len`, indexing (`xs[i]`), `++` and `==`; arrays of fixed-width numbers
# are packed.
module std.array

import std.list
import std.sort

# The list's elements, in order.
export fn from_list xs -> r : xs~List a, r~Array a, len r == list.length xs
    __builtin

# The array's elements, in order.
export fn to_list xs -> r : xs~Array a, r~List a, list.length r == len xs
    __builtin

# `n` copies of `x`.
export fn repeat n x -> r : n~Nat, x~a, r~Array a, len r == n
    __builtin

# `xs` with element `i` replaced by `x`. When nothing else refers to `xs`,
# it is updated in place; otherwise this copies it.
export fn set xs i x -> r : xs~Array a, i~Nat, i < len xs, x~a, r~Array a, len r == len xs, r[i] == x
    __builtin

# The elements from `i` up to (not including) `j`.
export fn slice xs i j -> r : xs~Array a, i~Nat, j~Nat, i <= j, j <= len xs, r~Array a, len r == j - i
    __builtin

# The arrays one after another, in time linear in the result.
export fn concat parts -> r : parts~List (Array a), r~Array a
    __builtin

# The elements in reverse order.
export fn reverse xs -> r : xs~Array a, r~Array a, len r == len xs
    __builtin

# `f` applied to each element, in order, written straight into the new
# array.
export fn map f xs -> r : f~(a -> b), xs~Array a, r~Array b, len r == len xs
    __builtin

# An array of `n` elements, element `i` being `f i`.
export fn init n f -> r : n~Nat, f~(Nat -> a), r~Array a, len r == n
    __builtin

# Whether `p` holds for every element (`True` for an empty array).
export fn all p xs -> r : p~(a -> Bool), xs~Array a, r~Bool
    all_from p xs 0

fn all_from p xs i -> r : p~(a -> Bool), xs~Array a, i~Nat, i <= len xs, r~Bool
    decreasing len xs - i
    if i < len xs then p xs[i] and all_from p xs (i + 1) else True

# Whether `x` is an element of `xs`.
export fn contains xs x -> r : xs~Array a, x~a, r~Bool
    contains_from xs x 0

fn contains_from xs x i -> r : xs~Array a, x~a, i~Nat, i <= len xs, r~Bool
    decreasing len xs - i
    if i < len xs then xs[i] == x or contains_from xs x (i + 1) else False

# How many times `x` occurs in `xs`.
export fn count x xs -> n : x~a, xs~Array a, n~Nat
    count_from x xs 0

fn count_from x xs i -> n : x~a, xs~Array a, i~Nat, i <= len xs, n~Nat
    decreasing len xs - i
    if i < len xs then (if xs[i] == x then 1 else 0) + count_from x xs (i + 1) else 0

# The first `n` elements, or all of `xs` if it is shorter.
export fn take n xs -> r : n~Nat, xs~Array a, r~Array a, len r <= len xs, n <= len xs implies len r == n
    slice xs 0 (if n <= len xs then n else len xs)

# All but the first `n` elements; empty if `xs` is shorter.
export fn drop n xs -> r : n~Nat, xs~Array a, r~Array a, len r <= len xs,
                           n <= len xs implies len r + n == len xs
    let k = if n <= len xs then n else len xs
    slice xs k (len xs)

# A list made into an array and back is the same list.
export lemma to_list_from_list xs : xs~List a
    ensures to_list (from_list xs) == xs
    proof
        __builtin

# An array made into a list and back is the same array.
export lemma from_list_to_list xs : xs~Array a
    ensures from_list (to_list xs) == xs
    proof
        __builtin

# `map` is `list.map` on the elements.
export lemma to_list_map f xs : f~(a -> b), xs~Array a
    ensures to_list (map f xs) == list.map f (to_list xs)
    proof
        __builtin

instance Functor Array
    fn fmap g xs
        map g xs
    lemma fmap_id xs
        proof
            have from_list_to_list (map (\x -> x) xs)
            have to_list_map (\x -> x) xs
            have list.map_id (to_list xs)
            have from_list_to_list xs
    lemma fmap_comp g h xs
        proof
            have from_list_to_list (map (\x -> g (h x)) xs)
            have from_list_to_list (map g (map h xs))
            have to_list_map (\x -> g (h x)) xs
            have to_list_map g (map h xs)
            have to_list_map h xs
            have list.map_comp g h (to_list xs)

# ── Sorting (D138) ───────────────────────────────────────────────────────────
# Stable, by the merge sorts of `std.sort`.

# `xs` in order (`Ord`).
export fn sort xs -> r : Ord a, xs~Array a, r~Array a, len r == len xs,
                         list.sorted (to_list r), list.perm (to_list xs) (to_list r)
    let s = sort.sort (to_list xs)
    have to_list_from_list s
    from_list s

# `xs` in the order of `key` of each element (`Ord`).
export fn sort_as key xs -> r : Ord k, key~(a -> k), xs~Array a, r~Array a, len r == len xs,
                                list.sorted_as key (to_list r), list.perm (to_list xs) (to_list r)
    let s = sort.sort_as key (to_list xs)
    have to_list_from_list s
    from_list s

# `xs` in the order `le` gives, which must put any two elements in order
# one way or the other (`total`).
export fn sort_by le xs -> r : le~(a -> a -> Bool), xs~Array a,
                               total: forall x y : x~a, y~a, le x y or le y x,
                               r~Array a, len r == len xs, list.sorted_by le (to_list r), list.perm (to_list xs) (to_list r)
    let s = sort.sort_by le (to_list xs)
    have to_list_from_list s
    from_list s

check to_list (from_list [3, 1, 2]) == [3, 1, 2]
check to_list (sort (from_list [3, 1, 2])) == [1, 2, 3]
check to_list (sort_by (\x y -> x >= y) (from_list [1, 3, 2])) == [3, 2, 1]
check len (repeat 4 7) == 4
check to_list (set (from_list [1, 2, 3]) 1 9) == [1, 9, 3]
check to_list (slice (from_list [1, 2, 3, 4]) 1 3) == [2, 3]
check to_list (concat [from_list [1, 2], from_list [], from_list [3]]) == [1, 2, 3]
check to_list (reverse (from_list [1, 2, 3])) == [3, 2, 1]
check to_list (map (\x -> x * 2) (from_list [1, 2, 3])) == [2, 4, 6]
check to_list (init 4 (\i -> i * i)) == [0, 1, 4, 9]
check len (init 0 (\i -> i)) == 0
check all (\x -> x > 0) (from_list [1, 2, 3]) and not (all (\x -> x > 1) (from_list [1, 2, 3]))
check contains (from_list [1, 2, 3]) 2 and not (contains (from_list [1, 2, 3]) 5)
check count 1 (from_list [1, 2, 1]) == 2
check to_list (take 2 (from_list [1, 2, 3])) == [1, 2] and to_list (take 5 (from_list [1])) == [1]
check to_list (drop 2 (from_list [1, 2, 3])) == [3] and to_list (drop 5 (from_list [1])) == []
check from_list [104, 105] == b"hi"
