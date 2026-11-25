# What `std.math`'s definitions and `pow`'s promises don't give: a fact
# about `pow n k` for every `k` needs induction.
module math_unknown

import std.math

fn min_left x y -> r : x~Int, y~Int, r~Int, r < x
    math.min x y

fn grows n k -> r : n~Int, n >= 2, k~Nat, r~Int, r > k
    math.pow n k
