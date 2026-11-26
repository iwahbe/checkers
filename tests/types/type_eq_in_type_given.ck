module type_eq_in_type_given

# A type equation in a type's header holds wherever a parameter has the
# type: `a == b` here.

record Same a b : a == b
    first~a
    second~b

fn second_as_first p -> r : p~Same a b, r~a
    p.second

fn flip p -> r : p~Same a b, r~Same b a
    Same p.second p.first

check second_as_first (Same 1 2) == 2
