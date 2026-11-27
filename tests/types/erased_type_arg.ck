module erased_type_arg

# A type passed as an erased argument uses nothing at run time, even the
# variables it is computed from (`a` in `wrap s a`, #672 c).

enum Shape
    One
    Many

fn wrap s a -> t : s~Shape, a~Type, t~Type
    match s
        One  -> a
        Many -> List a

fn keep x -> r : x~own a, r~a
    x

fn pass s x -> r : s~Shape, x~wrap s a, r~wrap s a
    keep x
