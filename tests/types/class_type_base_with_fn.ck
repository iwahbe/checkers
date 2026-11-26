module class_type_base_with_fn

# A base type together with a predicate through a class's function.

class Encoding s
    type Unit : u~Int, u >= 0, width s u < 3
    fn width s u -> n : s~ghost Type, u~Unit, n~Nat
    fn one x -> u : x~s, u~Unit

record Ascii
    first~U8

instance Encoding Ascii
    type Unit = U8
    fn width s u
        if u < 128 then 1 else 2
    fn one x
        x.first

fn narrow x -> r : Encoding s, x~s, r~Bool, r
    one x >= 0 and width s (one x) < 3

check narrow (Ascii 200)
