module class_alias_own_clause_proved

# A class's function with clauses of its own, at a refinement alias, whose
# instance promises values of the alias: accepted at a call, through the
# dictionary and partially applied.

class Tag a
    fn tag x -> b : x~a, b~Bool

instance Tag Bool
    fn tag x
        x

class Make t
    fn pair x y -> r : Tag a, Tag b, x~a, y~b, r~t

instance Make Int
    fn pair x y -> r : Tag a, Tag b, x~a, y~b, r~Int, r >= 0
        0

fn made x -> r : Make t, Tag a, x~a, r~t
    Make.pair x x

fn at_call -> n : n~Nat
    Make.pair True False

fn generic -> n : n~Nat
    made True

fn partially -> n : n~Nat
    let f = Make.pair True
    f False
