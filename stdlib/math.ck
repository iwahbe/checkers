# math.ck — functions on integers.
module std.math

# The smaller of `x` and `y`.
export transparent fn min x y -> r : x~Int, y~Int, r~Int
    if x <= y then x else y

# The larger of `x` and `y`.
export transparent fn max x y -> r : x~Int, y~Int, r~Int
    if x >= y then x else y

# `n` multiplied by itself `k` times: `pow n 0` is `1`, and
# `pow n (k + 1)` is `n * pow n k`.
export transparent fn pow n k -> r : n~Int, k~Nat, r~Int
    decreasing k
    if k == 0 then 1 else n * pow n (k - 1)

check min 3 5 == 3
check min (-2) 7 == -2
check max 3 5 == 5
check max (-2) (-7) == -2
check pow 2 10 == 1024
check pow (-3) 3 == -27
check pow 0 0 == 1
check pow 2 100 == 1267650600228229401496703205376
