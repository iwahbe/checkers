module class_instance

# An instance of a class from another module (D136): its lemma's
# diagnostic is at the instance, and the class's code shown there
# isn't indexed as if it were in this file.
record Odd
    n~Nat

instance Ord Odd
    fn le x y
        x.n <= y.n + 1
