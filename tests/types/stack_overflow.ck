module stack_overflow

# A `check` that recurses deeper than the stack holds is a runtime error of
# that `check` (E0261), not the end of `checkers`: the checks after it still
# run. `/` after the call keeps the recursion from becoming a loop.

fn deep n -> r : n~Nat, r~Nat
    if n == 0 then 0 else deep (n - 1) / 2

check deep 100000000 == 0
check deep 3 == 1
