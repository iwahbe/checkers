# A call to another module's function outside its precondition, which
# would end at once: its value isn't known, so it isn't a `Nat` by its
# value, and the result's obligation is reported with the call's
# precondition.
module known_precondition

import known.domain (next)

fn outside -> r : r~Nat
    next 0
