module termination

fn loops n -> m : n~Nat, m~Nat
    loops n

fn not_smaller xs -> n : xs~List Nat, n~Nat
    match xs
        []        -> 0
        x :: rest -> not_smaller (x :: rest)

fn structural xs -> n : xs~List Nat, n~Nat
    match xs
        []        -> 0
        _ :: rest -> 1 + structural rest

fn even xs -> b : xs~List Nat, b~Bool
    match xs
        []        -> True
        _ :: rest -> odd rest

fn odd xs -> b : xs~List Nat, b~Bool
    match xs
        []        -> False
        _ :: rest -> even rest

# Not structural, but has a measure: accepted now, proven in M5.
fn countdown n -> m : n~Nat, m~Nat
    decreasing n
    if n == 0 then 0 else countdown (n - 1)

partial fn forever n -> m : n~Nat, m~Nat
    forever (n + 1)

fn calls_partial n -> m : n~Nat, m~Nat
    forever n
