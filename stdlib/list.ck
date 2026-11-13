# list.ck — functions on immutable lists.
module std.list

import std.bag

# The number of elements.
export transparent fn length xs -> n : xs~List a, n~Nat
    match xs
        []        -> 0
        _ :: rest -> 1 + length rest

# `f` applied to each element, in order.
export transparent fn map f xs -> ys : f~(a -> b), xs~List a, ys~List b
    match xs
        []        -> []
        x :: rest -> f x :: map f rest

# Whether `p` holds for every element (`True` for an empty list).
export fn all p xs -> r : p~(a -> Bool), xs~List a, r~Bool
    match xs
        []        -> True
        x :: rest -> p x and all p rest

# The elements in reverse order.
export transparent fn reverse xs -> ys : xs~List a, ys~List a
    reverse_onto xs []

fn reverse_onto xs acc -> ys : xs~List a, acc~List a, ys~List a
    match xs
        []        -> acc
        x :: rest -> reverse_onto rest (x :: acc)

# The strings with `sep` between each two.
export transparent fn join sep parts -> s : sep~String, parts~List String, s~String
    match parts
        []        -> ""
        [p]       -> p
        p :: rest -> p ++ sep ++ join sep rest

# The first component of each pair.
export transparent fn keys pairs -> ks : pairs~List (k, v), ks~List k
    match pairs
        []               -> []
        (key, _) :: rest -> key :: keys rest

# Whether `x` is an element of `xs`.
export transparent fn contains xs x -> r : xs~List a, x~a, r~Bool
    match xs
        []        -> False
        y :: rest -> y == x or contains rest x

# Whether no element occurs twice.
export transparent fn unique xs -> r : xs~List a, r~Bool
    match xs
        []        -> True
        x :: rest -> not (contains rest x) and unique rest

# How many times `x` occurs in `xs`.
export transparent fn count x xs -> n : x~a, xs~List a, n~Nat
    match xs
        []        -> 0
        y :: rest -> (if y == x then 1 else 0) + count x rest

# The largest element, or 0 for an empty list.
export transparent fn max_of xs -> m : xs~List Nat, m~Nat
    match xs
        []        -> 0
        x :: rest ->
            let m = max_of rest
            if x > m then x else m

# The first `n` elements, or all of `xs` if it is shorter.
export fn take n xs -> ys : n~Nat, xs~List a, ys~List a,
                            length ys <= length xs, n <= length xs implies length ys == n
    match xs
        []        -> []
        x :: rest -> if n == 0 then [] else x :: take (n - 1) rest

# All but the first `n` elements; empty if `xs` is shorter.
export fn drop n xs -> ys : n~Nat, xs~List a, ys~List a,
                            length ys <= length xs, n <= length xs implies length ys + n == length xs
    match xs
        []        -> []
        _ :: rest -> if n == 0 then xs else drop (n - 1) rest

# Splitting a list and joining the halves gives it back.
export lemma take_drop n xs : n~Nat, xs~List a
    ensures take n xs ++ drop n xs == xs
    proof
        match xs
            []        -> auto
            _ :: rest ->
                match n
                    0 -> auto
                    _ -> have take_drop (n - 1) rest

# The elements of `xs ++ ys` are those of `xs` and those of `ys`.
export lemma bag_append xs ys : xs~List a, ys~List a
    ensures bag.of (xs ++ ys) == bag.sum (bag.of xs) (bag.of ys)
    proof
        match xs
            []        -> auto
            _ :: rest -> have bag_append rest ys

# Whether each element comes before the next or with it (`Ord`, D138).
export transparent fn sorted xs -> r : Ord a, xs~List a, r~Bool
    decreasing length xs
    match xs
        x :: y :: rest -> le x y and sorted (y :: rest)
        _              -> True

# Whether each element comes before the next or with it, by `le`.
export transparent fn sorted_by le xs -> r : le~(a -> a -> Bool), xs~List a, r~Bool
    decreasing length xs
    match xs
        x :: y :: rest -> le x y and sorted_by le (y :: rest)
        _              -> True

# Whether each element's key comes before the next one's or with it.
export transparent fn sorted_as key xs -> r : Ord k, key~(a -> k), xs~List a, r~Bool
    decreasing length xs
    match xs
        x :: y :: rest -> le (key x) (key y) and sorted_as key (y :: rest)
        _              -> True

# `ys` is a rearrangement of `xs`: the same elements, as often (D47).
export transparent fn perm xs ys -> r : xs~List a, ys~List a, r~Bool
    bag.of xs == bag.of ys

# The first element, if there is one.
export transparent fn head xs -> r : xs~List a, r~Option a
    match xs
        []     -> None
        x :: _ -> Some x

# Moving an element to the front keeps the same elements.
export lemma perm_middle xs y ys : xs~List a, y~a, ys~List a
    ensures perm (xs ++ (y :: ys)) (y :: (xs ++ ys))
    proof
        match xs
            []        -> auto
            _ :: rest -> have perm_middle rest y ys

# ── Lemmas about uniqueness and reversal ─────────────────────────────────────

# Adding a new element to a list without repeats keeps it without repeats.
export lemma unique_cons x xs : x~a, xs~List a, not (contains xs x), unique xs
    ensures unique (x :: xs)
    proof
        auto

# The maximum of a longer list is at least its head and the old maximum.
export lemma max_of_cons x xs : x~Nat, xs~List Nat
    ensures x <= max_of (x :: xs) and max_of xs <= max_of (x :: xs)
    proof
        auto

# Appending the empty list changes nothing.
export lemma append_nil xs : xs~List a
    ensures xs ++ [] == xs
    proof
        match xs
            []        -> auto
            _ :: rest -> have append_nil rest

# `++` is associative.
export lemma append_assoc xs ys zs : xs~List a, ys~List a, zs~List a
    ensures (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
    proof
        match xs
            []        -> auto
            _ :: rest -> have append_assoc rest ys zs

lemma rev_onto_app xs acc : xs~List a, acc~List a
    ensures reverse_onto xs acc == reverse_onto xs [] ++ acc
    proof
        match xs
            []        -> auto
            x :: rest ->
                have rev_onto_app rest (x :: acc)
                have rev_onto_app rest [x]
                have append_assoc (reverse_onto rest []) [x] acc

lemma keys_rev_onto ps acc : ps~List (k, v), acc~List (k, v)
    ensures keys (reverse_onto ps acc) == reverse_onto (keys ps) (keys acc)
    proof
        match ps
            []        -> auto
            p :: rest -> have keys_rev_onto rest (p :: acc)

# The keys of a reversed list are the reversed keys.
export lemma keys_reverse ps : ps~List (k, v)
    ensures keys (reverse ps) == reverse (keys ps)
    proof
        have keys_rev_onto ps []

lemma contains_rev_onto xs acc y : xs~List a, acc~List a, y~a
    ensures contains (reverse_onto xs acc) y == (contains xs y or contains acc y)
    proof
        match xs
            []        -> auto
            x :: rest -> have contains_rev_onto rest (x :: acc) y

# No element of `xs` is in `ys`.
fn disjoint xs ys -> r : xs~List a, ys~List a, r~Bool
    match xs
        []        -> True
        x :: rest -> not (contains ys x) and disjoint rest ys

lemma disjoint_nil xs : xs~List a
    ensures disjoint xs []
    proof
        match xs
            []        -> auto
            _ :: rest -> have disjoint_nil rest

lemma disjoint_cons xs ys x : xs~List a, ys~List a, x~a, disjoint xs ys, not (contains xs x)
    ensures disjoint xs (x :: ys)
    proof
        match xs
            []        -> auto
            _ :: rest -> have disjoint_cons rest ys x

lemma unique_rev_onto xs acc : xs~List a, acc~List a, unique xs, unique acc, disjoint xs acc
    ensures unique (reverse_onto xs acc)
    proof
        match xs
            []        -> auto
            x :: rest ->
                have disjoint_cons rest acc x
                have unique_rev_onto rest (x :: acc)

# Reversing keeps a list without repeats.
export lemma unique_reverse xs : xs~List a, unique xs
    ensures unique (reverse xs)
    proof
        have disjoint_nil xs
        have unique_rev_onto xs []

# Moving `x` from the reversed prefix onto the rest keeps the whole.
export lemma reverse_cons_append acc x rest : acc~List a, x~a, rest~List a
    ensures reverse (x :: acc) ++ rest == reverse acc ++ (x :: rest)
    proof
        have rev_onto_app acc [x]
        have append_assoc (reverse_onto acc []) [x] rest

# The keys of an append are the appended keys.
export lemma keys_append xs ys : xs~List (k, v), ys~List (k, v)
    ensures keys (xs ++ ys) == keys xs ++ keys ys
    proof
        match xs
            []        -> auto
            _ :: rest -> have keys_append rest ys

# An element of `xs ++ ys` is an element of `xs` or of `ys`.
export lemma contains_append xs ys y : xs~List a, ys~List a, y~a
    ensures contains (xs ++ ys) y == (contains xs y or contains ys y)
    proof
        match xs
            []        -> auto
            _ :: rest -> have contains_append rest ys y

# Reversing doesn't change which elements a list has.
export lemma contains_reverse xs y : xs~List a, y~a
    ensures contains (reverse xs) y == contains xs y
    proof
        have contains_rev_onto xs [] y

# In a list without repeats, an element is not also earlier in it.
export lemma unique_split xs y ys : xs~List a, y~a, ys~List a, unique (xs ++ (y :: ys))
    ensures not (contains xs y)
    proof
        match xs
            []        -> auto
            x :: rest ->
                have contains_append rest (y :: ys) x
                have unique_split rest y ys
