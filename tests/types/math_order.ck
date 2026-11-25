# `std.math`'s `min` and `max` work in any type's order: at a type
# parameter with `Ord`'s lemmas, at a known instance through its
# definitions.
module math_order

import std.math

record Rank
    n~Int

# Ranks by their number.
instance Ord Rank
    fn le x y
        x.n <= y.n

fn lower x y -> r : Ord a, x~a, y~a, r~a, r <= x, r <= y
    have refl x
    have refl y
    have total x y
    math.min x y

fn upper x y -> r : Ord a, x~a, y~a, r~a, x <= r, y <= r
    have refl x
    have refl y
    have total x y
    math.max x y

fn one_of x y -> r : Ord a, x~a, y~a, r~Bool, r
    math.min x y == x or math.min x y == y

fn of_strings s t -> r : s~String, t~String, r~String, r <= s, r <= t
    lower s t

fn of_ranks x y -> r : x~Rank, y~Rank, r~Rank, r.n <= x.n, r.n <= y.n
    math.min x y

fn of_ranks_max x y -> r : x~Rank, y~Rank, r~Int, r == x.n or r == y.n
    (math.max x y).n
