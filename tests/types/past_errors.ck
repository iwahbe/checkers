module past_errors

# Checking goes on past errors (D122): a syntax error and a type error, and
# still the other declarations' type errors, proofs and `check`s.

fn good x -> r : x~Nat, r~Nat
    x + 1

# A syntax error in the body: the header stays, so uses of `broken` see it.
fn broken x -> r : x~Nat, r~Nat
    x + + 1

# A type error.
fn mistyped x -> r : x~Nat, r~Nat
    "s"

# Proven and unproven as usual.
fn proven x -> r : x~Nat, r~Nat, r > x
    good x

fn unproven x -> r : x~Nat, r~Nat, r > 5
    x

# Set aside: they use a declaration with errors.
fn uses_broken x -> r : x~Nat, r~Nat, r > 100
    broken x + mistyped x

check broken 1 == 1
check mistyped 1 == 1

# Run as usual.
check good 1 == 3
check unproven 7 == 7
