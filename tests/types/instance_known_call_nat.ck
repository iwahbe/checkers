module instance_known_call_nat

# A call at a known instance has the instance's result type: where a `Nat`
# is needed, it must be one there, as the instance promises.

class Pos a
    fn pos w x -> r : w~a, x~Int, x > 0, r~Nat

record Box
    v~Int

instance Pos Box
    fn pos w x -> r : w~Box, x~Int, r~Int, r == x
        x

fn returned b -> r : b~Box, r~Nat
    pos b (-5)

fn need n -> r : n~Nat, r~Nat
    n

fn passed b -> r : b~Box, r~Nat
    need (pos b (-5))

# Where the instance's postcondition gives a `Nat`, it is one.
fn right b -> r : b~Box, r~Nat
    need (pos b 5)

# Where the instance isn't known where the call is written (a lambda's
# parameter, whose type a later use tells), the call has the class's result
# type, a `Nat` only where the class's precondition holds.
fn later b -> r : b~Box, r~Int
    let g = \w -> pos w (-5)
    g b
