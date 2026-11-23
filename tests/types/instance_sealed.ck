module instance_sealed

# A known instance's function from another module is sealed: its body is
# hidden, its signature (its own, or the class's) is known.

import class_home.sealed (Size, Box, Pos)

fn by_body b -> r : b~Box, r~Bool, r
    Size.size b == 1

fn by_signature p -> r : p~Pos, r~Bool, r
    Size.size p == 1
