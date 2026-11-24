# An instance for pairs covers every tuple: `(a, b, c)` is `(a, (b, c))`.
module instance_pair_tuples

class Size t
    fn size x -> n : x~t, n~Nat

instance Size Int
    fn size x
        1

instance Size (a, b) : Size b
    fn size p
        let (_, rest) = p
        1 + Size.size rest

check size (1, (2, 3)) == 3
check size (1, 2, 3) == 3
check size (1, 2, 3, 4) == 4
