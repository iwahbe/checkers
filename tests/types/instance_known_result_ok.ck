module instance_known_result_ok

# At a known instance, a call meeting only the instance's precondition
# gets the class's refined result type where the instance's signature
# promises it.

class Pos a
    fn pos w x -> r : w~a, x~Int, x > 0, r~Nat

record Box
    v~Int

instance Pos Box
    fn pos w x -> r : w~Box, x~Int, r~Nat
        if x > 0 then x else 0

record Pair
    v~Int

instance Pos Pair
    fn pos w x -> r : w~Pair, x~Int, r~Int, r == x * x
        x * x

fn by_type b -> r : b~Box, r~Nat
    pos b (-5)

fn by_post p -> r : p~Pair, r~Nat
    pos p (-5)

check by_type (Box 0) == 0
check by_post (Pair 0) == 25

type Small = n~Nat, n < 10

record Clamp
    v~Int

# A result of a refinement of the class's result type.
instance Pos Clamp
    fn pos w x -> r : w~Clamp, x~Int, r~Small
        0

fn by_refinement c -> r : c~Clamp, r~Nat
    pos c (-5)

check by_refinement (Clamp 0) == 0
