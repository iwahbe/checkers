module instance_refined_body

# The body is checked against the instance's own signature.

class Size a
    fn size x -> n : x~a, n~Int

record Box
    v~Int

instance Size Box
    fn size b -> n : b~Box, n~Int, n >= 0
        b.v
