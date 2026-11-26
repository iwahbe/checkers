module class_type_pred_applied

import std.list (length)

# A predicate on a class's type that passes the class's parameter is
# checked at an instance for a type with parameters (`Box b`): the
# parameter is the instance's type, not a value.

class Short s
    type Run : r~Run, size s r < 3
    fn size s r -> n : s~ghost Type, r~Run, n~Nat

record Box b
    item~b

instance Short (Box b)
    type Run = List (Box b)
    fn size s r
        length r % 3
