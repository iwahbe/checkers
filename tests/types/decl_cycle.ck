module decl_cycle

# What depends on itself is an error (D65).

let A = B + 1
let B = A * 2

# The signature of `f` needs LIMIT, which needs f's value.
fn f n -> m : n~Nat, m~Nat, m <= LIMIT
    n

let LIMIT = f 3

# An invariant that uses a function on the record itself.
record Box
    v~Nat, small (Box v)

fn small b -> r : b~Box, r~Bool
    b.v < 10
