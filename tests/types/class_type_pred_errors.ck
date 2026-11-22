module class_type_pred_errors

# A class's type's predicates must follow from each instance's type.

class Encoding s
    type Unit : u~Unit, u < 256
    fn units x -> us : x~s, us~List Unit

record Wide
    text : List Nat

instance Encoding Wide
    type Unit = Nat
    fn units w
        w.text

# A default that doesn't satisfy them: reported once, in the class.
class Small s
    type Digit = Nat : d~Digit, d < 10
    fn digit x -> d : x~s, d~Digit

# Only what is declared is known.
fn byte u -> b : Encoding s, u~Encoding.Unit s, b~U8
    if u < 128 then u else u - 128

fn small u -> b : Encoding s, u~Encoding.Unit s, b~Nat
    u - 200
