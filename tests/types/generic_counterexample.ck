# A counterexample through generic code holds values of the types the code
# is used at: each element of an array is one of its element type, however
# the code reaches it.
module generic_counterexample

fn ordered_from xs i -> r : Ord a, xs~Array a, i~Nat, i <= len xs, r~Bool
    decreasing len xs - i
    if len xs <= i + 1 then True else Ord.le xs[i] xs[i + 1] and ordered_from xs (i + 1)

fn at_bytes xs -> r : xs~Bytes, 1 < len xs, r~Bool, r
    ordered_from xs 0

fn at_digits xs -> r : xs~Array (n~Int, 0 <= n, n <= 9), 1 < len xs, r~Bool, r
    ordered_from xs 0
