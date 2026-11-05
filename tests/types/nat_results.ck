module nat_results

# Prover soundness: "the result is a Nat" is a fact about well-typed calls
# that meet the precondition, not about every value the solver can invent.
# Each `bad_*` must be reported; each `good_*` must be proved.

fn pred n -> m : n~Nat, n > 0, m~Nat
    n - 1

fn width lo hi -> w : lo~Nat, hi~Nat, lo <= hi, w~Nat
    hi - lo

fn first o -> n : o~Option Nat, n~Nat
    match o
        None   -> 0
        Some k -> k

fn bad_pre -> m : m~Nat
    pred 0                                  # 0 > 0 is false

fn bad_width -> w : w~Nat
    width 5 3                               # 5 <= 3 is false

fn bad_first o -> b : o~Option Nat, b~Bool, b
    first o > 0                             # o may be None

fn good_first o -> b : o~Option Nat, b~Bool, b
    first o >= 0
