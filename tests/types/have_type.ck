module have_type

# `have x~T` (D170): `x`'s type is `T`. It settles what is still unknown of
# `x`'s type (a literal's, before it would become a `Nat`), and a refinement
# it adds is an obligation, then a fact.

type Percent = n~Nat, n <= 100

fn below x -> r : x~Int, r~Int
    let y = 5
    have y~Int
    let z = y - 7
    z + x

fn half p -> q : p~Nat, p <= 50, q~Percent
    let d = p * 2
    have d~Percent
    d

fn empty -> n : n~Nat
    let xs = []
    have xs~List String
    len xs

fn unproven p -> q : p~Nat, q~Nat
    have p~Percent
    p

fn mismatch x -> r : x~Int, r~Int
    have x~String
    x

check below 1 == -1
check half 50 == 100
check empty == 0
