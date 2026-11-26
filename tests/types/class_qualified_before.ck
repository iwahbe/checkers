module class_qualified_before

# A class's function or lemma named by its class (`C.f`) above the class:
# checked as it is below the class, or unqualified. Each call here breaks
# its promise or its callee's, or doesn't say which instance it means.

fn qualified -> r : r~Int, r == 6
    Make.make 5

fn as_value -> r : r~Int, r == 6
    let f = Make.make
    f 5

fn by_type -> r : r~Nat
    Read.read (-1) Nat

let UNKNOWN = Make.make 5

fn by_lemma x -> r : x~Int, r~Int
    have Make.pos x (-1)
    x

class Make t
    fn make u -> r : u~Int, r~t
    lemma pos x y : x~t, y~Int, y > 0
        ensures y >= 1

instance Make Int
    fn make u
        u
    lemma pos x y
        proof
            auto

class Read t
    fn read x t -> r : x~Int, t~ghost Type, r~t

instance Read Int
    fn read x t -> r : x~Int, t~ghost Type, r~Int, r == x
        x
