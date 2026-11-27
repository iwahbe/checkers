# #673: `(a, b, c)` is `(a, (b, c))`, and a pattern may take a tuple apart
# into fewer parts, its last the rest.
module tuples_nested

import std.string (debug)

fn rest p -> r : p~(a, b, c), r~(b, c)
    let (_, more) = p
    more

fn swap_tail p -> r : p~(a, (b, c)), r~(a, c, b)
    let (x, y, z) = p
    (x, z, y)

check rest (1, 2, 3) == (2, 3)
check swap_tail (1, 2, 3) == (1, 3, 2)
check (1, (2, 3)) == (1, 2, 3)
check debug (1, (2, 3)) == "(1, 2, 3)"

fn pair x t -> r : x~a, t~b, r~(a, b)
    (x, t)

check pair 1 (2, 3) == (1, 2, 3)

# Arms may take the tuple apart into different numbers of parts.
fn first_or_sum p -> r : p~(Int, Int, Int), r~Int
    match p
        (0, rest) -> 0
        (a, b, c) -> a + b + c

check first_or_sum (0, 5, 6) == 0
check first_or_sum (1, 2, 3) == 6

# Too many parts for the type is still an error.
fn too_many p -> r : p~(Int, Int), r~Int
    let (a, b, c) = p
    a
