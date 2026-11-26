module type_clause_wanted

# A class clause in a type's header is a condition on the type: wherever the
# type is written with arguments, or a value of it is built, its instance
# must exist.

record Packed s : Seq s
    items~s

fn at_signature p -> r : p~Packed Int, r~Int
    0

record Holder
    inner~Packed Int

fn at_construction x -> r : x~Int, r~Int
    (Packed x).items
