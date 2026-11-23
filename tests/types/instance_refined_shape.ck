module instance_refined_shape

# An instance's signature has the class's parameters and types, up to
# refinement: `Nat` for `Int` is allowed, `Bool` is not.

class Size a
    fn size x -> n : x~a, n~Int

record A
    v~Int

instance Size A
    fn size x -> n : x~A, n~Nat
        0

record C
    v~Int

instance Size C
    fn size x extra -> n : x~C, extra~Int, n~Int
        0

record D
    v~Int

instance Size D
    fn size x -> n : x~D, n~Bool
        True

record E
    v~Int

instance Size E
    fn size x -> n : x~ghost E, n~Int
        0
