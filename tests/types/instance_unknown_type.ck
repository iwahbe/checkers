module instance_unknown_type

# An instance for a type that isn't declared: the type is unknown, whether
# the class has lemmas or not, and whether the instance gives its functions.

instance Ord Nope
    fn le p q
        True

instance Ord Gone

instance Add Missing
    fn add p q
        p

# An alias, whose own declaration is wrong.
type Age = Int

instance Ord Age
    fn le p q
        True
