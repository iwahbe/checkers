module refined_deep_fn

# A function's result is compared however many parameters come before it:
# `bad`'s `Int` result is not the `Nat` that `apply` expects.

fn bad x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> r : x0~Int, x1~Int, x2~Int, x3~Int, x4~Int, x5~Int, x6~Int, x7~Int, x8~Int, x9~Int, x10~Int, x11~Int, x12~Int, x13~Int, x14~Int, x15~Int, x16~Int, r~Int
    -1

fn apply f -> r : f~(Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Nat), r~Nat
    f 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

fn use -> r : r~Nat
    apply bad
