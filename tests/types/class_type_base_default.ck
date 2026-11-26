module class_type_base_default

# A default type is checked against the base type at each instance that
# takes it.

class Measure s
    type Size = Int : n~Nat
    fn size x -> n : x~s, n~Size

instance Measure String
    type Size = U8
    fn size x
        0

instance Measure Bool
    fn size x
        0
