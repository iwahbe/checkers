module type_eq_inconsistent

# Type equations that contradict each other: the body never runs, and no
# call meets them.

fn never t -> r : t~ghost Type, t == Int, t == Bool, r~Nat
    0

check never Int == 0
