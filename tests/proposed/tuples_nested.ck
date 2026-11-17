# D174 (proposed): `(a, b, c)` is `(a, (b, c))`.
module tuples_nested

fn rest p -> r : p~(a, b, c), r~(b, c)
    let (_, more) = p
    more

fn swap_tail p -> r : p~(a, (b, c)), r~(a, c, b)
    let (x, y, z) = p
    (x, z, y)

check rest (1, 2, 3) == (2, 3)
check swap_tail (1, 2, 3) == (1, 3, 2)
check (1, (2, 3)) == (1, 2, 3)
check format (1, (2, 3)) == "(1, 2, 3)"

# Expected: 0 errors.
