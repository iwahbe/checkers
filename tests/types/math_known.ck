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

# What `pow` promises: never negative for a base that isn't, positive for
# a positive base. So `pow 10 k` is a `Nat` of at least 1, and bounds one.
fn positive n k -> r : n~Int, n > 0, k~Nat, r~Nat, r > 0
    math.pow n k

fn ten k -> r : k~Nat, r~Nat, r >= 1
    math.pow 10 k

fn digit_of r f -> d : r~Nat, f~Nat, r < math.pow 10 f, d~Nat, d < math.pow 10 f
    r

fn by_ten r f -> q : r~Nat, f~Nat, q~Nat
    r / math.pow 10 f

# A fact for every `k` that `pow` doesn't promise needs induction.
lemma pow_grows n k : n~Int, n >= 2, k~Nat
    ensures math.pow n k > k
    proof
        decreasing k
        if k > 0
            have pow_grows n (k - 1)
        else
            auto
