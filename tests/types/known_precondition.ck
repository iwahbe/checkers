# Calls to another module's functions outside their preconditions: their
# values aren't known, and aren't computed. `half 0` wouldn't end; `next 0`
# would end at once, so the result's obligation isn't met by its value.
module known_precondition

import known.domain (half, next)

fn endless n -> r : n~Nat, r~Nat
    half 0 + n

fn outside -> r : r~Nat
    next 0
