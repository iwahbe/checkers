module class_relational_pre

# A class function's precondition relating two of its parameters: an
# instance's function has the class's signature, so it may assume it, and
# each call must establish it.

class Pick a
    fn pick w n x -> r : w~a, n~Nat, x~Nat, x <= n, r~Nat

record Box
    v~Int

instance Pick Box
    fn pick w n x
        n - x

fn good b -> r : b~Box, r~Nat
    pick b 2 1

fn bad b -> r : b~Box, r~Nat
    pick b 1 2
