# Values whose making only this module sees: importers know what the
# signatures say.
module sealed.boxes

import std.list (length)

export record Box a
    item~a

export record Counted a
    count~Nat
    items~List a, length items == count

export fn boxed -> b : b~Box Nat
    Box 3

export fn counted xs -> c : xs~List a, c~Counted a
    Counted (length xs) xs

export fn below i n -> r : i~Nat, n~Nat, i < n, r~Box (j~Nat, j < n)
    Box i

export fn find k -> r : k~Nat, r~Option (Box (Box (s~Nat, k < s)))
    Some (Box (Box (k + 1)))

export fn pair k -> r : k~Nat, r~Box (Bool, (s~Nat, k < s))
    Box (False, k + 1)
