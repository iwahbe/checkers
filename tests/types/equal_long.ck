module equal_long

# `==` takes stack independent of the values' size, as building them does:
# along a list (the last field) and along a chain nested in the first field.

enum Snoc
    Lin
    Snoc s n : s~Snoc, n~Nat

fn long n -> r : n~Nat, r~List Nat
    if n == 0 then [] else 1 :: long (n - 1)

fn snoc_onto s n -> r : s~Snoc, n~Nat, r~Snoc
    decreasing n
    if n == 0 then s else snoc_onto (Snoc s 1) (n - 1)

check long 4000000 == long 4000000
check snoc_onto Lin 4000000 == snoc_onto Lin 4000000
check long 3 == [1, 1, 1]
