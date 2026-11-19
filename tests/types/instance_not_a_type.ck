module instance_not_a_type

# An instance whose head is a name but not a type: `Type`, or a constructor,
# here or imported. Whether the class has lemmas or not, and whether the
# instance gives its functions, only the head is reported.

instance Ord Type
    fn le p q
        True

instance Ord Type

instance Add Type
    fn add p q
        p

instance Monoid Type
    fn zero
        0

enum Shape
    Dot

instance Ord Dot
    fn le p q
        True

instance Ord Some
    fn le p q
        True
