module known_value_nat

# A non-negative value known at compile time is a `Nat` by construction, as a
# non-negative literal is: returning it as a `Nat` leaves nothing to prove.

import std.math

fn by_call k -> r : k~Int, r~Nat
    if k < 0 then math.pow 2 3 else 0
