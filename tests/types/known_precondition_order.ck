# A call to another module's function is computed at compile time where
# its preconditions hold on its arguments, in order: `b > 0` holds for
# `second 0 100`, so its value is known, and fits in a `U8`.
module known_precondition_order

import known.pair (second)

fn byte x -> r : x~U8, r~U8
    x

fn known -> r : r~U8
    byte (second 0 100)
