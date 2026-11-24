module instance_refined_value_result

# A class's result type promises its refinement only where the class's
# preconditions hold. An instance dropping a precondition doesn't make a
# value of its function give that refinement without it: the value keeps
# the class's signature.

record Box
    v~Int

class Pos a
    fn pos w x -> r : w~a, x~Int, x > 0, r~Nat

instance Pos Box
    fn pos w x -> r : w~Box, x~Int, r~Int, x > 0 implies r >= 0
        x

fn by_value b -> r : b~Box, r~Nat
    let f = pos b
    f (-5)
