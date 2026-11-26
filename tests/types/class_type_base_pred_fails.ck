module class_type_base_pred_fails

# An instance's type must satisfy the predicates on the base type.

class Encoding s
    type Unit : u~Int, u < 256
    fn one x -> u : x~s, u~Unit

record Utf16
    first~U16

instance Encoding Utf16
    type Unit = U16
    fn one x
        x.first
