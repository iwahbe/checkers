module class_type_base_not_base

# An instance's type must be the base type, or a refinement of it.

class Encoding s
    type Unit : u~Int, u < 256
    fn one x -> u : x~s, u~Unit

record Words
    text~String

instance Encoding Words
    type Unit = String
    fn one x
        x.text
