# What `std.math`'s definitions don't give: `pow n k > 0` needs induction.
module math_unknown

import std.math

fn min_left x y -> r : x~Int, y~Int, r~Int, r < x
    math.min x y

fn positive n k -> r : n~Int, n > 0, k~Nat, r~Int, r > 0
    math.pow n k
