module instance_known_result

# At a known instance whose function requires less than its class's, a
# call meeting only the instance's precondition doesn't get the class's
# refined result type.

class Pos a
    fn pos w x -> r : w~a, x~Int, x > 0, r~Nat

record Box
    v~Int

instance Pos Box
    fn pos w x -> r : w~Box, x~Int, r~Int, x > 0 implies r >= 0
        x

fn wrong b -> r : b~Box, r~Nat
    pos b (-5)

# Where the class's precondition holds, the result is a `Nat`.
fn right b -> r : b~Box, r~Nat
    pos b 5

check right (Box 0) == 5

# A refinement inside the result: the same.
class Wrapped a
    fn wrapped w x -> r : w~a, x~Int, x > 0, r~Option Nat

instance Wrapped Box
    fn wrapped w x -> r : w~Box, x~Int, r~Option (n~Int, x > 0 implies n >= 0)
        Some x

fn wrong_inside b -> r : b~Box, r~Option Nat
    wrapped b (-5)

fn right_inside b -> r : b~Box, r~Option Nat
    wrapped b 5

# Under a recursive type: only where the class's precondition holds.
class Listed a
    fn listed w x -> r : w~a, x~Int, x > 0, r~List Nat

instance Listed Box
    fn listed w x -> r : w~Box, x~Int, r~List (n~Int, x > 0 implies n >= 0)
        [x]

fn wrong_list b -> r : b~Box, r~List Nat
    listed b (-5)

fn right_list b -> r : b~Box, r~List Nat
    listed b 5
