module class_type_pred

# A class's type may have predicates (`type Unit : u~Unit, u < 256`): each
# instance's type must satisfy them, and generic code assumes them.

class Encoding s
    type Unit : u~Unit, u < 256
    fn units x -> us : x~s, us~List Unit

record Ascii
    text : String

instance Encoding Ascii
    type Unit = U8
    fn units a
        array.to_list a.text.bytes

# A default is checked once, in the class.
class Small s
    type Digit = U8 : d~Digit, d < 1000
    fn digit x -> d : x~s, d~Digit

instance Small Int
    fn digit x
        if 0 <= x and x < 256 then x else 0

# Each value of `Encoding.Unit s` is `< 256`: a parameter, an element,
# a result.
fn byte u -> b : Encoding s, u~Encoding.Unit s, b~U8
    u

fn first x -> b : Encoding s, x~s, b~U8
    match units x
        []     -> 0
        u :: _ -> u

fn all_bytes x -> bs : Encoding s, x~s, bs~List U8
    match units x
        []      -> []
        u :: us -> u :: map byte us

check first (Ascii "hi") == 104
