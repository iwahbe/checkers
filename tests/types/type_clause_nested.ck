module type_clause_nested

# A class clause in a type's header holds wherever a parameter's type has
# the type, at any depth.

record Packed s : Seq s
    items~s

fn sizes ps -> r : ps~List (Packed s), r~List Nat
    match ps
        []        -> []
        p :: rest -> Seq.size p.items :: sizes rest

check sizes [Packed [1, 2], Packed [3]] == [2, 1]
