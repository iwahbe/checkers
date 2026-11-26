module type_clause_fields

# A class clause in a type's header holds in its fields: a field's
# refinement may use the class, and that refinement is known where a value
# of the type is taken apart.

record NonEmpty s : Seq s
    items~s, Seq.size items > 0

fn size p -> n : p~NonEmpty s, n~Nat, n > 0
    Seq.size p.items

check size (NonEmpty [1, 2]) == 2
