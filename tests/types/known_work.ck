# Types and proofs compute a value known at compile time to completion,
# however long it takes: `spin 20000000` is 0, so a `Nat` by its value, as
# `spin 1000` is.
module known_work

import known.domain (spin)

fn within -> r : r~Nat
    spin 1000

fn beyond -> r : r~Nat
    spin 20000000
