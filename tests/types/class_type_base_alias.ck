module class_type_base_alias

# A base type that is a refinement alias: an instance's type must have its
# refinement too.

class Count s
    type Item : i~Nat
    fn item x -> i : x~s, i~Item

instance Count Bool
    type Item = U8
    fn item x
        if x then 1 else 0

instance Count String
    type Item = Int
    fn item x
        0

fn natural x -> n : Count s, x~s, n~Nat
    item x
