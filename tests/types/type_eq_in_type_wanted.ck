module type_eq_in_type_wanted

# A type equation in a type's header is a condition on the type: wherever
# the type is written with arguments, or a value of it is built, it must
# hold.

record Same a b : a == b
    first~a
    second~b

fn differ -> r : r~Same Int Bool
    Same 1 True

fn built x -> r : x~Int, r~Int
    (Same x True).first
