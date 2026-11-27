module effect_deep

# A call given a capability inside 40 `Option`s has effects: two such
# calls may return different values.

import std.terminal (Term)

fn need x y -> r : x~a, y~a, x == y, r~Unit
    ()

fn read t -> r : t~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Term)))))))))))))))))))))))))))))))))))))))), r~Nat
    0

fn twice t -> r : t~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Term)))))))))))))))))))))))))))))))))))))))), r~Unit
    need (read t) (read t)
