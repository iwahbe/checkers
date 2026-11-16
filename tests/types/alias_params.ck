module alias_params

# A type alias's parameters may be values: each parameter's type is what
# the alias's definition makes it (`lo <= n` with `n~Int` makes `lo` an
# `Int`), and `Type` when nothing decides. A failed refinement is shown in
# the use's names (`b <= 10`), not the alias's (`n <= hi`).

type Bounded lo hi = n~Int, lo <= n, n <= hi

type Pairs a = xs~List (a, a)

fn mid -> b : b~Bounded 0 10
    5

fn clamp lo hi x -> r : lo~Int, hi~Int, lo <= hi, x~Int, r~Bounded lo hi
    if x < lo then lo else if x > hi then hi else x

fn widen x -> y : x~Bounded 2 5, y~Bounded 0 10
    x

fn swap ps -> qs : ps~Pairs Int, qs~Pairs Int
    ps

fn too_big -> b : b~Bounded 0 10
    11

fn narrow x -> y : x~Bounded 0 10, y~Bounded 2 5
    x

check mid == 5
check clamp 0 3 7 == 3
check swap [(1, 2)] == [(1, 2)]
