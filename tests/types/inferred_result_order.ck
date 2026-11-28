module inferred_result_order

# A function whose result type isn't written is checked before the
# functions that use it (#557), so its result type is known at each call,
# whatever the arguments.

fn uses_later prev pending -> r : prev~Option Nat, pending~Bool, r~Bool
    let keep = pending and at_most prev 1
    keep

fn at_most prev l : prev~Option Nat, l~Nat
    match prev
        Some q -> l <= q
        None   -> False

# Between functions that call each other, one is checked first: its call
# to the other, not yet checked, gives that one's result type (one type for
# every call, whatever the arguments).
fn even n : n~Nat
    decreasing n
    if n == 0 then True else odd (n - 1)

fn odd n : n~Nat
    decreasing n
    if n == 0 then False else even (n - 1)

check even 4
check not (odd 4)
