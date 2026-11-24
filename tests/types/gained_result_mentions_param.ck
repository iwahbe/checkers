module gained_result_mentions_param

# A function's result refinement that mentions its parameter, not gained
# from a `let`-bound lambda: shown with the parameter in scope.

fn apply f -> r : f~(x~Nat -> y~Nat, y <= x), r~Nat
    f 0

fn caller -> r : r~Nat
    let same = \x -> x
    apply same                                  # error E0262: `Nat` results aren't known to be `y <= x`
