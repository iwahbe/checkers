module operators

# Operators on types other than numbers (M24): `+ - *` and negation through
# the prelude's classes `Add`, `Sub`, `Mul` and `Neg`, comparisons through
# `Ord`, and `Monoid`'s lemmas used in a proof.

record V2
    x~Int
    y~Int

instance Add V2
    fn add a b
        V2 (a.x + b.x) (a.y + b.y)

instance Sub V2
    fn sub a b
        V2 (a.x - b.x) (a.y - b.y)

instance Neg V2
    fn neg a
        V2 (0 - a.x) (0 - a.y)

# Its lemmas, `assoc`, `zero_add` and `add_zero`, are proved here.
instance Monoid V2
    fn zero
        V2 0 0

# Generic: `+` and `zero` of any monoid.
fn sum xs -> r : Add a, Monoid a, xs~List a, r~a
    match xs
        []        -> zero
        x :: rest -> x + sum rest

# A monoid's lemma, used.
lemma sum_pair x y : Add a, Monoid a, x~a, y~a
    ensures sum [x, y] == x + y
    proof
        have Monoid.add_zero y

fn moved p d -> r : p~V2, d~V2, r~V2, r - d == p
    p + d

# Comparisons through `Ord`: strings, lists, and a type of the program's own.
record Version
    major~Nat
    minor~Nat

instance Ord Version
    fn le v w
        v.major < w.major or (v.major == w.major and v.minor <= w.minor)

fn newer v w -> r : v~Version, w~Version, r~Version, v <= r and w <= r
    if v < w then w else v

check sum [V2 1 2, V2 3 4] == V2 4 6 and sum [1, 2, 3] == 6
check -(V2 1 2) == V2 (-1) (-2) and V2 5 5 - V2 1 2 == V2 4 3
check "apple" < "banana" and [1, 2] <= [1, 3] and not ([2] < [1, 9])
check newer (Version 1 2) (Version 1 10) == Version 1 10
