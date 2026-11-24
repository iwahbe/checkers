module class_type_pred

import std.list (map)
import std.array

# A class's type may have predicates (`type Unit : u~Unit, code s u < 256`),
# about its values through the class's functions: each instance's type must
# satisfy them, and generic code assumes them.

class Encoding s
    type Unit : u~Unit, code s u < 256
    fn code s u -> n : s~ghost Type, u~Unit, n~Nat
    fn units x -> us : x~s, us~List Unit

record Ascii
    text~String

instance Encoding Ascii
    type Unit = U8
    fn code s u
        u
    fn units a
        array.to_list a.text.bytes

# A default is checked once, in the class.
class Small s
    type Digit = U8 : d~Digit, value s d < 1000
    fn value s d -> n : s~ghost Type, d~Digit, n~Nat
    fn digit x -> d : x~s, d~Digit

instance Small Int
    fn value s d
        d
    fn digit x
        if 0 <= x and x < 256 then x else 0

# Each value of `Encoding.Unit s` satisfies them: a parameter, an
# element, a result.
fn byte u -> b : Encoding s, u~Encoding.Unit s, b~U8
    code s u

fn first x -> b : Encoding s, x~s, b~U8
    match units x
        []     -> 0
        u :: _ -> code s u

fn all_bytes x -> bs : Encoding s, x~s, bs~List U8
    map (\u -> byte u) (units x)

check first (Ascii "hi") == 104
check all_bytes (Ascii "ok") == [111, 107]
