module type_eq_in_type_wanted

# A type equation in a type's header is a condition on the type: wherever
# the type is written with arguments, or a value of it is built, it must
# hold.

record Packed s : Seq s, Seq.Elem s == U8
    bytes~s

fn chars -> r : r~Packed String
    Packed "ab"

fn built x -> r : x~String, r~String
    (Packed x).bytes
