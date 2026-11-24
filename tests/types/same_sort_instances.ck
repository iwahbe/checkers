# `String` and `Bytes` are one sort to the prover: a function used at
# both is defined once in the query.
module same_sort_instances

fn size xs -> n : xs~List a, n~Nat
    match xs
        []        -> 0
        _ :: rest -> 1 + size rest

fn at_both ss bs -> r : ss~List String, bs~List Bytes, size ss > 0, size bs > 0, r~Bool, r
    size ss > 0 and size bs > 0
