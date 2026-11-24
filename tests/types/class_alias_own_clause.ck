module class_alias_own_clause

# A class's function with clauses of its own, used at a refinement alias:
# its result is checked as without them, at a call (the class's type
# inferred or passed explicitly), through the dictionary, and for its
# function parameters.

class Tag a
    fn tag x -> b : x~a, b~Bool

instance Tag Bool
    fn tag x
        x

class Make t
    fn make x t -> r : Tag a, x~a, t~ghost Type, r~t
    fn pair x y -> r : Tag a, Tag b, x~a, y~b, r~t
    fn test x f -> b : Tag a, x~a, f~(t -> Bool), b~Bool

instance Make Int
    fn make x t
        -1
    fn pair x y
        -1
    fn test x f
        f (-1)

fn explicit -> n : n~Nat
    Make.make True Nat

fn inferred -> n : n~Nat
    Make.pair True False

fn made x -> r : Make t, Tag a, x~a, r~t
    Make.pair x x

fn generic -> n : n~Nat
    made True

fn small n -> b : n~Nat, b~Bool
    n < 10

fn parameter -> b : b~Bool
    Make.test True small
