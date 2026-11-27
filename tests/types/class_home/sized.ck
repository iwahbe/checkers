# A class with a type, a function and a lemma, for a module that names it
# through this module's qualifier.
module class_home.sized

export class Sized a
    type Part
    fn size x -> n : x~a, n~Int
    lemma pos x : x~a
        ensures size x >= 0

instance Sized Bool
    type Part = Int
    fn size b
        if b then 1 else 0
