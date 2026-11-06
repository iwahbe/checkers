module const_in_signature

# A constant computed by a function can't size a signature: signatures are
# checked before function bodies run. The error says so.

let LIMIT = double 50

fn double n -> m : n~Nat, m~Nat
    2 * n

fn clamp n -> m : n~Nat, m~Nat, m <= LIMIT
    if n <= LIMIT then n else LIMIT
