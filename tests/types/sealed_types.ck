module sealed_types

# A sealed function doesn't unfold in types either (D54): `two` is not `2`
# here, while the transparent `three` is `3`.

import sealed_lib (two, three)

enum Tag n : n~Nat
    T

fn shown t -> u : t~Tag three, u~Tag 3
    t

fn sealed t -> u : t~Tag two, u~Tag 2
    t
