module asked

# Proved by the first query.
fn proved x -> r : x~Int, r~Int, r > x
    x + 1

# A counterexample.
fn refuted x -> r : x~Int, r~Int, r > x
    x

# A path condition among the facts.
fn branch x -> r : x~Int, r~Int, r >= 0
    if x > 0 then x else 0
