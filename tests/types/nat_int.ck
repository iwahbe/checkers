module nat_int

# `Nat` is a refinement of `Int` (D121).

# (a) A `Nat` is an `Int`: free, also inside a type, and the two mix.
fn widen n -> i : n~Nat, i~Int
    n

fn widen_all ns -> is : ns~List Nat, is~List Int
    ns

fn mixed n i -> r : n~Nat, i~Int, r~Int
    n + i - 3

# (b) An `Int` where a `Nat` is expected is a proof obligation, not a type
# error: proven here by the `if`, unproven in `narrow_wrong`.
fn narrow i -> r : i~Int, r~Option Nat
    if i >= 0 then Some i else None

fn narrow_wrong i -> r : i~Int, r~Nat
    i

# (c) Arithmetic on `Nat`s gives a `Nat` with no obligation, except `-`.
fn closed a b -> r : a~Nat, b~Nat, r~Nat
    a * b + a / (b + 1) + a % (b + 1) + 7

fn minus a b -> r : a~Nat, b~Nat, r~Nat
    a - b

# A refinement is never gained inside a type (D71 c).
fn narrow_all is -> ns : is~List Int, ns~List Nat
    is

# (d) A function over `Nat`s is a `Nat -> Nat`, also where its type is
# inferred first and `f` must then have it (`a` from `inc`, then `f~a`).
fn inc x -> r : x~Nat, r~Nat
    x + 1

fn same_type x y : x~a, y~a
    True

fn inc_first f : f~(Nat -> Nat)
    same_type inc f

fn inc_listed f : f~(Nat -> Nat)
    same_type [inc] [f]
