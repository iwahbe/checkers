module refined_deep_container

# A refinement is compared however deeply it is nested: an `Int` inside
# 17 `Option`s is not a `Positive` there.

type Positive = n~Int, n > 0

fn keep x -> r : x~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Int))))))))))))))))), r~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Positive)))))))))))))))))
    x
