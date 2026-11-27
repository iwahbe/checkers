module refined_deep_nested

# Deeply nested refinements are compared, not skipped: a `Positive` inside
# 40 `Option`s is a `Nat` there, and an `Int` is not.

type Positive = n~Int, n > 0

fn weaken x -> r : x~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Positive)))))))))))))))))))))))))))))))))))))))), r~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Nat))))))))))))))))))))))))))))))))))))))))
    x

fn gain x -> r : x~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Int)))))))))))))))))))))))))))))))))))))))), r~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Nat))))))))))))))))))))))))))))))))))))))))
    x
