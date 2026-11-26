module type_eq_in_type_nested

# A type equation in a type's header holds wherever a parameter's type has
# the type, at any depth.

record Same a b : a == b
    first~a
    second~b

fn seconds ps -> r : ps~List (Same a b), r~List a
    match ps
        []        -> []
        p :: rest -> p.second :: seconds rest

check seconds [Same 1 2, Same 3 4] == [2, 4]
