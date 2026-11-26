# An arm no value reaches never runs: what it would have to
# prove holds, and its calls are not recursion. Each arm below gets only
# W021, no proof error and no E0301.
module unreachable_arm_never_runs

fn positive n -> r : n~Int, n > 0, r~Int
    n

fn vacuous x -> r : x~Int, r~Int
    match x
        _ -> 0
        y -> positive y

fn loop n -> r : n~Nat, r~Nat
    match n
        _ -> 0
        m -> loop m
