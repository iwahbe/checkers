module known_facts

# The prover knows the value of a call known at compile time, though its
# function is sealed: a caller proves a bound written as such a call without
# testing it.

import std.array
import known.limits

fn under_count a -> r : a~Nat, a < array.count 7 (array.repeat 256 7), r~Nat
    a

fn under_power a -> r : a~Nat, a < limits.power_of_two 8, r~Nat
    a

fn callers -> r : r~Nat
    under_count 255 + under_power 255
