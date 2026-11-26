module type_clause_class_fn

# A class's function whose signature mentions a type with a class clause in
# its header has the clause implied, as any function does.

record Packed s : Seq s
    items~s

class Measure t
    fn measure p -> n : p~Packed t, n~Nat

instance Measure (List a)
    fn measure p
        Seq.size p.items

fn twice p -> n : Measure t, p~Packed t, n~Nat
    measure p + measure p

check twice (Packed [1, 2]) == 4
