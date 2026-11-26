module type_eq_in_type_given

# A type equation in a type's header holds wherever a parameter has the
# type: here the elements are `U8`s, so below 256.

record Packed s : Seq s, Seq.Elem s == U8
    bytes~s

fn first_or_zero p -> r : p~Packed s, r~Nat, r < 256
    match p.bytes
        []     -> 0
        x :: _ -> x

check first_or_zero (Packed [7, 8]) == 7
