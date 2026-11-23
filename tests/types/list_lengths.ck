# `std.list` says how long `xs ++ ys`, `reverse xs`, `map f xs` and
# `keys ps` are, and what `take` and `drop` give past the end.
module list_lengths

import std.list

# The `i`-th element, which exists.
fn at xs i -> r : xs~List a, i~Nat, i < list.length xs, r~a
    match list.head (list.drop i xs)
        Some x -> x

fn by_append xs ys i -> r : xs~List a, ys~List a, i~Nat, i < list.length xs, r~a
    have list.length_append xs ys
    at (xs ++ ys) i

fn by_reverse xs i -> r : xs~List a, i~Nat, i < list.length xs, r~a
    have list.length_reverse xs
    at (list.reverse xs) i

fn by_map f xs i -> r : f~(a -> b), xs~List a, i~Nat, i < list.length xs, r~b
    have list.length_map f xs
    at (list.map f xs) i

# `map` gives its function only elements of the list; so does `length_map`.
fn element xs x -> r : xs~List a, x~a, list.contains xs x, r~a
    x

fn by_map_within xs i -> r : xs~List a, i~Nat, i < list.length xs, r~a
    have list.length_map (\x -> element xs x) xs
    at (list.map (\x -> element xs x) xs) i

fn by_keys ps i -> r : ps~List (k, v), i~Nat, i < list.length ps, r~k
    have list.length_keys ps
    at (list.keys ps) i

fn drop_past_end n xs -> r : n~Nat, xs~List a, list.length xs <= n, r~List a, r == []
    list.drop n xs

fn take_past_end n xs -> r : n~Nat, xs~List a, list.length xs <= n, r~List a, r == xs
    list.take n xs
