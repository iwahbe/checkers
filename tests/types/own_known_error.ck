module own_known_error

# A function with an error gives no value known at compile time, and its
# error is reported once, where it is: `wrong` breaks its postcondition, so
# `WRONG` isn't known (running `wrong 6` would give 4), and `by_constant`
# can't use its value.

import std.array

fn wrong k -> r : k~Nat, r~Int, r != 4
    array.count 7 (array.repeat k 7) - 2

let WRONG = wrong 6

fn by_constant k -> r : k~Int, r~Nat
    if k < 0 then WRONG else 0
