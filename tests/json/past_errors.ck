module past_errors

# A syntax error, and still a proof failure and a false `check` in the other
# declarations (D122): each in its phase.

fn broken x -> r : x~Nat, r~Nat
    x + + 1

fn unproven x -> r : x~Nat, r~Nat, r > 5
    x

check unproven 1 == 2
