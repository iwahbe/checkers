module past_errors

# A syntax error and a proof failure, shown together (D122).
fn broken x -> r : x~Nat, r~Nat
    x + + 1

fn unproven x -> r : x~Nat, r~Nat, r > 5
    x
