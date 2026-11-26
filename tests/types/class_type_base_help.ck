module class_type_base_help

# Without a base type, an operator on a class's type's values in its
# predicates is an error, whose help shows both ways to say it.

class Encoding s
    type Unit : u~Unit, u < 256
    fn one x -> u : x~s, u~Unit
