# A hidden local's number isn't a name in scope: not one the module
# declares (`a1`), nor one it imports (`a2`).
module same_name_in_scope

import same_name.numbers (a2)

fn a1 -> r : r~Int
    0

fn hidden a x -> r : a~Type, x~a, r~Int
    let f = \a ->
        have x~Int
        0
    f Int
