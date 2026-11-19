# A refinement in a signature may mention a later parameter (#102).
module later_param_refinement

# `f` is called only below `n`, given after it.
fn under f n -> r : f~(i~Int -> Int, i < n), n~Int, r~Int
    if 0 < n then f 0 else 0

fn small i -> r : i~Int, i < 3, r~Int
    i

# `n` is checked first, then `small` against `(i~Int, i < 3)`.
fn by_name -> r : r~Int
    under small 3

# A lambda's parameter gets the refinement.
fn by_lambda -> r : r~Int
    under (\i -> small i) 3

# Passed on with a smaller bound: `i < n - 1` implies `i < n`.
fn down f n -> r : f~(i~Nat -> Nat, i < n), n~Nat, r~Nat
    if n == 0 then 0 else f (n - 1) + down f (n - 1)

# An element type's refinement, too.
fn first xs n -> r : xs~List (i~Int, i < n), n~Int, r~Int, r < n + 1
    match xs
        []    -> n
        x :: _ -> x

# The body calls `f` outside the bound.
fn at_bound f n -> r : f~(i~Int -> Int, i < n), n~Int, r~Int
    f n

# `small` doesn't accept `3`.
fn too_wide -> r : r~Int
    under small 4

# Without `n`, `small` must accept every `Int`.
fn partial_use -> r : r~(Int -> Int)
    under small
