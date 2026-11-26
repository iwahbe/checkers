module class_type_base_cycle

# A base type can't reach its own type, through the class's other types.

class Loop s
    type A : a~List B
    type B : b~List A
    fn a x -> r : x~s, r~A
