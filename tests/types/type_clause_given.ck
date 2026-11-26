module type_clause_given

# A class clause in a type's header holds wherever a parameter has the
# type: here `Seq s`, and the equation that uses it.

record Packed s : Seq s, Seq.Elem s == U8
    bytes~s

fn first p -> r : p~Packed s, r~Option U8
    match p.bytes
        []     -> None
        x :: _ -> Some x

check first (Packed [1, 2]) == Some 1
