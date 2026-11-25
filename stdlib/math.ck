# math.ck — order and integer arithmetic.
module std.math

# The smaller of `x` and `y` in their type's order: `x` if `x <= y`,
# else `y`.
export transparent fn min x y -> r : Ord a, x~a, y~a, r~a
    if x <= y then x else y

# The larger of `x` and `y` in their type's order: `x` if `x >= y`,
# else `y`.
export transparent fn max x y -> r : Ord a, x~a, y~a, r~a
    if x >= y then x else y

# `min x y` comes before or with `x`.
export lemma min_le_left x y : Ord a, x~a, y~a
    ensures min x y <= x
    proof
        have refl x
        have total x y

# `min x y` comes before or with `y`.
export lemma min_le_right x y : Ord a, x~a, y~a
    ensures min x y <= y
    proof
        have refl y

# `max x y` comes after or with `x`.
export lemma le_max_left x y : Ord a, x~a, y~a
    ensures x <= max x y
    proof
        have refl x
        have total x y

# `max x y` comes after or with `y`.
export lemma le_max_right x y : Ord a, x~a, y~a
    ensures y <= max x y
    proof
        have refl y

# `n` multiplied by itself `k` times: `pow n 0` is `1`, and
# `pow n (k + 1)` is `n * pow n k`.
export transparent fn pow n k -> r : n~Int, k~Nat, r~Int
    decreasing k
    if k == 0 then 1 else n * pow n (k - 1)

check min 3 5 == 3
check min (-2) 7 == -2
check max 3 5 == 5
check max (-2) (-7) == -2
check min "b" "a" == "a"
check max [1, 2] [1, 3] == [1, 3]
check pow 2 10 == 1024
check pow (-3) 3 == -27
check pow 0 0 == 1
check pow 2 100 == 1267650600228229401496703205376
