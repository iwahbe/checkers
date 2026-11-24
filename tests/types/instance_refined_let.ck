module instance_refined_let

# A partial application of a class's function whose instance is known
# where it is written has that instance's signature: here, no precondition
# on the parameter it still takes.

class Pick a
    fn pick w x -> r : w~a, x~Int, x > 0, r~Int

record Box
    v~Int

instance Pick Box
    fn pick w x -> r : w~Box, x~Int, r~Int
        x

fn by_let b -> r : b~Box, r~Int
    let f = pick b
    f 0
