module instance_refined_weaker

# An instance's signature can't drop a postcondition of the class's.

class Count a
    fn count x -> n : x~a, n~Int, n > 0

record Box
    v~Int

instance Count Box
    fn count b -> n : b~Box, n~Int
        1
