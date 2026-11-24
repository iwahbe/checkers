module instance_refined_imported

# An instance whose function has a signature of its own, in an imported
# module: this module's declarations aren't checked against its class.

import class_home.refined (Size)

fn g0 x -> r : x~Int, r~Bool
    x > 0

fn g1 x -> r : x~Int, r~Bool
    x > 1

fn g2 x -> r : x~Int, r~Bool
    x > 2

fn known b -> n : b~Bool, n~Int, n >= 0
    Size.size b
