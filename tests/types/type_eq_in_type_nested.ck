module type_eq_in_type_nested

# A type equation in a type's header holds wherever a parameter's type has
# the type, at any depth.

record Packed s : Seq s, Seq.Elem s == U8
    bytes~s

fn firsts ps -> r : ps~List (Packed s), r~List U8
    match ps
        []        -> []
        p :: rest ->
            match p.bytes
                []     -> firsts rest
                x :: _ -> x :: firsts rest

check firsts [Packed [1, 2], Packed [], Packed [3]] == [1, 3]
