module condition_type_error

# A condition with a type error is reported once, as a type error: the
# prover isn't asked about it, neither at a call nor whether the
# conditions can all hold.

record Box
    n~Int

fn need x y -> r : x~Box, y~Box, x < y, r~Bool
    True

fn walk x y -> r : x~Box, y~Box, r~Bool
    need x y
