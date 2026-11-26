module class_type_base

# A class's type may have a base type: each instance's type refines it,
# and generic code uses its values as the base's.

class Encoding s
    type Unit : u~Int, u < 256
    fn one x -> u : x~s, u~Unit

record Utf8
    first~U8

instance Encoding Utf8
    type Unit = U8
    fn one x
        x.first

fn direct x -> b : Encoding s, x~s, b~U8
    one x

fn next x -> n : Encoding s, x~s, n~Int
    one x + 1

fn small x -> r : Encoding s, x~s, r~Bool, r
    one x < 256

fn listed x -> r : Encoding s, x~s, r~List Int
    [one x, 300]

check direct (Utf8 7) == 7
check next (Utf8 255) == 256
check listed (Utf8 1) == [1, 300]
