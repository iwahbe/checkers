# Where a proof depends on a function another package keeps private, the
# error speaks of what this module calls, not of that function.
module private_std_limit

import std.time (Instant)

# `<=` on strings is built on a private function of the prelude.
fn by_operator x y -> r : x~String, y~String, len x.bytes < len y.bytes, r~Bool, r
    x <= y

# A value of an abstract type is made by a private constructor: a
# counterexample doesn't show it, but shows which such values are equal.
fn apart a b c -> r : a~Instant, b~Instant, c~Instant, a == b, r~Bool, r
    a == c or b == c
