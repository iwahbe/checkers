module class_type_base_one_way

# A class's type is a subtype of its base, not the other way: a value of
# the base isn't one of its values, at the top or inside another type, and
# two of them at different types differ.

class Encoding s
    type Unit : u~Int, u < 256
    fn one x -> u : x~s, u~Unit

fn literal x -> u : Encoding s, x~s, u~Encoding.Unit s
    3

fn from_int n -> u : Encoding s, n~Int, u~Encoding.Unit s
    n

fn from_list ns -> us : Encoding s, ns~List Int, us~List (Encoding.Unit s)
    ns

fn other x y -> u : Encoding s, Encoding t, x~s, y~t, u~Encoding.Unit s
    one y

fn kept x -> us : Encoding s, x~s, us~List (Encoding.Unit s)
    [one x, one x]
