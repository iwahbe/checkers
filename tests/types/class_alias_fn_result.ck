module class_alias_fn_result

# A class used at a refinement alias whose function gives a function giving
# values of the class's type: the instance's signature must promise that
# function's results are of the alias, by a refined function type.
# `Plain`'s doesn't.

class Maker t
    fn maker -> r : r~(Int -> t)

instance Maker Int
    fn maker -> r : r~(x~Int -> y~Int, y >= 0)
        \x -> 0

class Boxed t
    fn boxed u -> r : u~Int, r~Option (Int -> t)

instance Boxed Int
    fn boxed u -> r : u~Int, r~Option (x~Int -> y~Int, y >= 0)
        Some (\x -> 0)

class Plain t
    fn plain u -> r : u~Int, r~Option (Int -> t)

instance Plain Int
    fn plain u
        Some (\x -> x)

fn made -> f : f~(Int -> Nat)
    maker

fn in_option -> f : f~Option (Int -> Nat)
    boxed 1

fn unpromised -> f : f~Option (Int -> Nat)
    plain 1
