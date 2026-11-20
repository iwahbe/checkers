# An instance's tuple has two parts: `(a, b, c)` is `(a, (b, c))`.
module instance_tuple_head

class Size t
    fn size x -> n : x~t, n~Nat

instance Size (a, b, c)
    fn size p
        3
