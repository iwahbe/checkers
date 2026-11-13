# Unknown types in messages (D141): an unknown standing for a function's
# type parameter is shown by its name, `?f`; a mismatch that follows from
# an unknown already in a reported error isn't reported again.
module unknowns

fn doubled xs -> ys : Functor f, xs~f Int, ys~f Int
    fmap (\x -> x * 2) xs

fn size xs -> n : xs~f a, n~Nat
    0

fn first xs -> r : xs~List a, r~Option a
    match xs
        []     -> None
        x :: _ -> Some x

# One error: the result's mismatch, and the missing instance, follow from it.
fn one x -> n : x~Int, n~Int
    doubled x

fn two n -> b : n~Nat, b~Bool
    size n == 0

# `a` is this function's own type parameter: no `?`.
fn three xs -> b : xs~List a, b~Bool
    first xs == 5

# Not a type constructor's: the unknown is still named.
fn four x -> b : x~Int, b~Bool
    first x == None
