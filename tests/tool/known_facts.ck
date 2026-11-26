module known_facts

# The value of a call known at compile time, given to the prover, is in the
# trust ledger as computed.

import std.array

fn under_count a -> r : a~Nat, a < array.count 7 (array.repeat 256 7), r~Nat
    a

fn caller -> r : r~Nat
    under_count 255
