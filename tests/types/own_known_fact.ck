module own_known_fact

# The prover is given the value of a call of a function of the module being
# checked, once that function is proved, as for an imported function's: `a`
# is below `size 256`, which is 256, so it is a `U8`. The body of `size`
# calls a sealed function, so the prover doesn't see its value otherwise.

import std.array

fn size k -> r : k~Nat, r~Nat
    array.count 7 (array.repeat k 7)

fn by_call a -> r : a~Nat, a < size 256, r~U8
    a
