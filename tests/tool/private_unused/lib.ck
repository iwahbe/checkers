module lib

# Not called by `main`, but exported.
export fn offered n -> r : n~Nat, r~Nat
    helper n

# Reached from an export.
fn helper n -> r : n~Nat, r~Nat
    n + 1

# Reached from nothing.
fn dead n -> r : n~Nat, r~Nat
    n + 2
