module instance_known_call_type

# A call at a known instance whose function requires less than its class's
# has the instance's result type, as the function as a value has: where
# only an `Int` is needed, the class's `Nat` isn't.

class Pos a
    fn pos w x -> r : w~a, x~Int, x > 0, r~Nat

record Box
    v~Int

instance Pos Box
    fn pos w x -> r : w~Box, x~Int, r~Int, r == x
        x

fn direct b -> r : b~Box, r~Int
    pos b (-5)

fn by_value b -> r : b~Box, r~Int
    let f = pos b
    f (-5)

fn by_let b -> r : b~Box, r~Int
    let n = pos b (-5)
    n + 1

check direct (Box 0) == -5
check by_value (Box 0) == -5
check by_let (Box 0) == -4
