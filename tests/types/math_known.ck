# On `Int`s, `std.math`'s `min`, `max` and `pow` are known to the prover
# by their definitions.
module math_known

import std.math

fn min_left x y -> r : x~Int, y~Int, r~Int, r <= x
    math.min x y

fn min_right x y -> r : x~Int, y~Int, r~Int, r <= y
    math.min x y

fn max_either x y -> r : x~Int, y~Int, r~Bool, r
    math.max x y == x or math.max x y == y

fn max_above x y -> r : x~Int, y~Int, r~Int, x <= r, y <= r
    math.max x y

fn of_naturals x y -> r : x~Nat, y~Nat, r~Nat
    math.min x y

fn by_literals -> r : r~Bool, r
    math.pow 2 10 == 1024

fn by_zero n -> r : n~Int, r~Bool, r
    math.pow n 0 == 1

fn by_step n k -> r : n~Int, k~Nat, r~Bool, r
    math.pow n (k + 1) == n * math.pow n k

# A positive number to any power is positive.
lemma pow_positive n k : n~Int, n > 0, k~Nat
    ensures math.pow n k > 0
    proof
        decreasing k
        if k > 0
            have pow_positive n (k - 1)
        else
            auto

fn positive n k -> r : n~Int, n > 0, k~Nat, r~Nat, r > 0
    have pow_positive n k
    math.pow n k
