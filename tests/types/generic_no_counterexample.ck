# Where every counterexample Z3 finds holds elements no value of the type
# has, the error says there is none. Every byte is at most 255, but the
# prover doesn't know it of the elements generic code reaches.
module generic_no_counterexample

fn all_le xs m i -> r : Ord a, xs~Array a, m~a, i~Nat, i <= len xs, r~Bool
    decreasing len xs - i
    if len xs <= i then True else Ord.le xs[i] m and all_le xs m (i + 1)

fn bytes_below xs -> r : xs~Bytes, r~Bool, r
    all_le xs 255 0
