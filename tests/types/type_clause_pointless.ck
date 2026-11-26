module type_clause_pointless

# A class clause in a type's header must be about the type's parameters.

record Boxed a : Ord Int
    item~a
