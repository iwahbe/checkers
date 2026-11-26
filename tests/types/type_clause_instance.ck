module type_clause_instance

# An instance for a type with a class clause in its header writes the type
# with arguments: its context gives the clause, else it is missing there.

record Packed s : Seq s
    items~s

class Sized t
    fn sized x -> n : x~t, n~Nat

instance Sized (Packed s) : Seq s
    fn sized x
        Seq.size x.items

record Boxed s : Seq s
    items~s

instance Sized (Boxed s)
    fn sized x
        0

check Sized.sized (Packed [1, 2, 3]) == 3
