module instance_sealed_same_module

# In its own module an instance's function is visible without
# `transparent`.

class Size a
    fn size x -> n : x~a, n~Int

record Box
    v~Int

instance Size Box
    fn size b
        1

fn by_body b -> r : b~Box, r~Bool, r
    Size.size b == 1
