module type_function_long

fn deep n -> r : n~Nat, r~Type
    if n == 0 then Int else deep (n - 1)

fn use x -> r : x~deep 250000, r~Int
    x
