module class_alias_function

# A class's function taking a function of the class's type, used at a
# refinement alias: the instance must be shown to call it only with values
# of the alias, which a signature of its own says.

class Test t
    fn test f -> b : f~(t -> Bool), b~Bool

instance Test Int
    fn test f
        f (-1)

class Probe t
    fn probe f -> b : f~(t -> Bool), b~Bool

instance Probe Int
    fn probe f -> b : f~(Nat -> Bool), b~Bool
        f 3

fn small n -> b : n~Nat, b~Bool
    n < 10

fn by_any -> b : b~Bool
    Test.test small

fn by_signature -> b : b~Bool
    Probe.probe small
