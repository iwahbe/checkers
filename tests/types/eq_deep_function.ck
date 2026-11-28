module eq_deep_function

# `==` can't compare a type holding a function, however deep the
# function is: here inside 40 `Option`s.

fn same a b -> r : a~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Int -> Int)))))))))))))))))))))))))))))))))))))))), b~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Int -> Int)))))))))))))))))))))))))))))))))))))))), r~Bool
    a == b
