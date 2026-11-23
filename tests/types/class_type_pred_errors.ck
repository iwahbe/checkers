module class_type_pred_errors

# A class's type's predicates must follow from each instance's type.

class Encoding s
    type Unit : u~Unit, code s u < 256
    fn code s u -> n : s~ghost Type, u~Unit, n~Nat
    fn units x -> us : x~s, us~List Unit

record Wide
    text~List Nat

instance Encoding Wide
    type Unit = Nat
    fn code s u
        u
    fn units w
        w.text

# A default that doesn't satisfy them: reported at each instance taking it,
# whose functions the predicates use.
class Small s
    type Digit = Nat : d~Digit, value s d < 10
    fn value s d -> n : s~ghost Type, d~Digit, n~Nat
    fn digit x -> d : x~s, d~Digit

instance Small Int
    fn value s d
        d
    fn digit x
        if 0 <= x and x < 10 then x else 0

# Only what is declared is known.
fn small u -> b : Encoding s, u~Encoding.Unit s, b~Nat
    code s u - 200

# A class's type is a type of its own: a predicate reaches its values
# through the class's functions.
class Numeric s
    type Unit : u~Unit, u < 256
    fn pick x -> u : x~s, u~Unit
