module class_alias_inline

# A class's function taking a function of the class's type, used at a
# refinement alias, where the instance's signature writes its parameter as
# a refined function type: its precondition, which may mention another
# parameter (`Above`), must imply the alias's.

class Probe t
    fn probe f -> b : f~(t -> Bool), b~Bool

instance Probe Int
    fn probe f -> b : f~(x~Int -> Bool, x >= 0), b~Bool
        f 3

class Above t
    fn above lo f -> b : lo~Nat, f~(t -> Bool), b~Bool

instance Above Int
    fn above lo f -> b : lo~Nat, f~(x~Int -> Bool, x >= lo), b~Bool
        f lo

class Loose t
    fn loose f -> b : f~(t -> Bool), b~Bool

instance Loose Int
    fn loose f -> b : f~(x~Int -> Bool, x >= -1), b~Bool
        f 3

fn small n -> b : n~Nat, b~Bool
    n < 10

fn by_refined -> b : b~Bool
    Probe.probe small

fn by_parameter -> b : b~Bool
    Above.above 3 small

fn by_weaker -> b : b~Bool
    Loose.loose small
