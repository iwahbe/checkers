module known.limits

# Sealed: a module importing this one sees its signature, not its body.
export fn power_of_two k -> r : k~Nat, r~Nat
    decreasing k
    if k == 0 then 1 else 2 * power_of_two (k - 1)
