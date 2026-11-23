module function_arg_post_fails

# A call of a function parameter with a function value argument has only
# what the parameter's type promises: nothing follows from the function
# passed, and the parameter's type still obliges that function's own.
fn only_promised body -> r : body~(f~(k~Nat -> j~Nat) -> n~Nat, n > 3), r~Nat, r == 5
    body (\k -> 5)

fn distinct_calls body -> r : body~(f~(k~Nat -> j~Nat) -> n~Nat, n > 3), r~Bool, r
    body (\k -> k) == body (\k -> k + 1)

fn obliged body -> r : body~(f~(k~Nat -> j~Nat, j > k) -> n~Nat, n > 3), r~Nat, r > 3
    body (\k -> k)

fn met body -> r : body~(f~(k~Nat -> j~Nat, j > k) -> n~Nat, n > 3), r~Nat, r > 3
    body (\k -> k + 1)
