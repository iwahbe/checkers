module known.domain

# `next 0` is outside its precondition, and would end at once with 1.
export fn next x -> r : x~Int, x >= 1, r~Int
    x + 1

# Ends after `n` calls, with 0.
export fn spin n -> r : n~Nat, r~Int
    decreasing n
    if n == 0 then 0 else spin (n - 1)
