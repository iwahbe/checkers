# A `match` covers the values that can occur (D144): a case left out is an
# obligation that it can't occur there.
module uncovered

enum Color
    Red
    Green
    Blue

# The precondition rules out `[]`.
fn head xs -> r : xs~List Int, xs != [], r~Int
    match xs
        x :: _ -> x

# And `Blue`, here.
fn warm c -> r : c~Color, c != Blue, r~Bool
    match c
        Red   -> True
        Green -> False

# An earlier test rules out the rest.
fn describe n -> s : n~Nat, s~String
    if n < 2
        match n
            0 -> "none"
            1 -> "one"
    else
        "many"

# Nothing rules out `Blue` here.
fn cool c -> r : c~Color, r~Bool
    match c
        Green -> True
        Red   -> False
