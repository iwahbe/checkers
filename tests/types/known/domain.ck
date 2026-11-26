module known.domain

# `half 0` is outside its precondition, and doesn't end.
export fn half x -> r : x~Nat, x >= 1, r~Nat
    decreasing x
    if x == 1 then 0 else 1 + half (x / 2)

# `next 0` is outside its precondition, and would end at once with 1.
export fn next x -> r : x~Int, x >= 1, r~Int
    x + 1

# Ends after `n` calls, with 0.
export fn spin n -> r : n~Nat, r~Int
    decreasing n
    if n == 0 then 0 else spin (n - 1)
