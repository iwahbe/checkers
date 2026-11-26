module type_clause_instance

# An instance whose head mentions a type with a class clause in its header
# has the clause implied in its context, and its functions have it too.

record Packed s : Seq s
    items~s

class Sized t
    fn sized x -> n : x~t, n~Nat

instance Sized (Packed s)
    fn sized x
        Seq.size x.items

fn total p -> n : p~Packed s, n~Nat
    Sized.sized p

check Sized.sized (Packed [1, 2, 3]) == 3
check total (Packed "ab") == 2
