module instance_refined_pre

# An instance may drop a precondition of the class's, and a call at the
# known instance needs only the instance's, wherever the instance is
# declared. It can't add one.

class Pick a
    fn pick w x -> r : w~a, x~Int, x > 0, r~Int

record Box
    v~Int

fn zero b -> r : b~Box, r~Int
    pick b 0

instance Pick Box
    fn pick w x -> r : w~Box, x~Int, r~Int
        x

fn also_zero b -> r : b~Box, r~Int
    pick b 0

record Cell
    v~Int

instance Pick Cell
    fn pick w x -> r : w~Cell, x~Int, x > 1, r~Int
        x

fn generic w -> r : Pick a, w~a, r~Int
    pick w 0
