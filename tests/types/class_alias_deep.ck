module class_alias_deep

# A class's function whose parameter takes a function giving values of the
# class's type: at a refinement alias, the instance hands it such a
# function, so its signature must promise that function gives values of
# the alias. `Bound`'s does; `Visit`'s doesn't.

class Visit t
    fn visit f -> b : f~((Int -> t) -> Bool), b~Bool

instance Visit Int
    fn visit f
        f (\x -> x)

class Bound t
    fn bound f -> b : f~((Int -> t) -> Bool), b~Bool

instance Bound Int
    fn bound f -> b : f~((x~Int -> y~Int, y >= 0) -> Bool), b~Bool
        f (\x -> 0)

fn at_zero g -> b : g~(Int -> Nat), b~Bool
    g 0 == 0

fn by_any -> b : b~Bool
    Visit.visit at_zero

fn by_signature -> b : b~Bool
    Bound.bound at_zero
