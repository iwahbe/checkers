module type_function_never_ends

fn grow n -> r : n~Nat, r~Type
    grow (n + 1)

fn use x -> r : x~grow 0, r~grow 0
    x
