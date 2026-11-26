# A value known at compile time is computed within a work limit: `spin`
# ends, but `spin 20000000` takes more than the limit, so its value isn't
# known and the result's obligation is reported. `spin 1000` is known: 0,
# a `Nat`.
module known_work

import known.domain (spin)

fn within -> r : r~Nat
    spin 1000

fn beyond -> r : r~Nat
    spin 20000000
