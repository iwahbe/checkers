module unsolved_in_match

# A type the checker can't work out is reported (E0203) inside an `if` or a
# `match` in a signature as it is outside one (D178).

fn phantom xs -> t : xs~List a, t~Type
    Nat

fn plain x -> n : x~phantom [], n~Nat
    0

fn hidden b x -> n : b~Bool, x~(if b then phantom [] else Nat), n~Nat
    0
