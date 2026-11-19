module lib

# Used by `main`.
export fn used n -> r : n~Nat, r~Nat
    n + 1

# Used by no module of the package: still part of its interface.
export fn offered n -> r : n~Nat, r~Nat
    n + 2
