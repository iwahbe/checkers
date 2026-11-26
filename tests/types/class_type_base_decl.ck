module class_type_base_decl

# A base type is one type: not two, and not one naming the class's
# parameter. Naming the type itself as well says the same.

class Both s
    type Unit : u~Unit, u~Int, u < 256
    fn both x -> u : x~s, u~Unit

class Two s
    type Unit : u~Int, u~Nat
    fn two x -> u : x~s, u~Unit

class Mine s
    type Unit : u~List s
    fn mine x -> u : x~s, u~Unit

fn small x -> r : Both s, x~s, r~Bool, r
    both x < 256
