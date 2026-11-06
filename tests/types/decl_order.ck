module decl_order

# Declarations are checked in the order of what they use, not of the file
# (D65): each may use any declaration that doesn't depend on it.

# A constant computed by a function declared later, used in a signature.
let LIMIT = double 50

fn clamp n -> m : n~Nat, m~Nat, m <= LIMIT
    if n <= LIMIT then n else LIMIT

fn double n -> m : n~Nat, m~Nat
    2 * n

# Constants in any order.
let TOTAL = PART + PART
let PART = double 3

check TOTAL == 12

# A type computed by a function declared later.
fn first_of xs -> v : xs~Pair, v~Nat
    match xs
        Pair a _ -> a

record Pair
    a~Nat
    b~Nat, b >= half LIMIT

fn half n -> m : n~Nat, m~Nat
    n / 2

# Recursion between bodies is fine, in either order.
fn is_even n -> b : n~Nat, b~Bool
    decreasing n
    if n == 0 then True else is_odd (n - 1)

fn is_odd n -> b : n~Nat, b~Bool
    decreasing n
    if n == 0 then False else is_even (n - 1)
