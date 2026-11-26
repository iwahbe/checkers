module type_eq_rejected

# Type equations that can't be written: one that makes a type contain
# itself, and one about the result.

fn loops t -> r : t~ghost Type, t == List t, r~Nat
    0

fn promises x -> r : x~Int, r~ghost Type, r == Int
    Int
