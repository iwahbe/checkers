module instance_refined_value_known

# A known instance's function as a value has the instance's signature, its
# result type included: a call meeting only the instance's precondition
# gives what the instance promises, not the class's `Nat`.

record Box
    v~Int

class Pos a
    fn pos w x -> r : w~a, x~Int, x > 0, r~Nat

instance Pos Box
    fn pos w x -> r : w~Box, x~Int, r~Int, x > 0 implies r >= 0
        x

fn by_let b -> r : b~Box, r~Nat
    let f = pos b
    f (-5)

fn by_let_int b -> r : b~Box, r~Int
    let f = pos b
    f (-5)

fn by_let_pos b -> r : b~Box, r~Nat
    let f = pos b
    f 5

fn apply g -> r : g~(Int -> Nat), r~Nat
    g (-5)

fn passed b -> r : b~Box, r~Nat
    apply (pos b)

fn apply_pos g -> r : g~(x~Int -> Nat, x > 0), r~Nat
    g 5

fn passed_pos b -> r : b~Box, r~Nat
    apply_pos (pos b)

check by_let_int (Box 0) == -5
check by_let_pos (Box 0) == 5
check passed_pos (Box 0) == 5
