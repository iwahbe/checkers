module function_arg_post

# A call of a function parameter has the postcondition its type promises
# when an argument is a function value: a lambda, or a function by name.
fn by_lambda body -> r : body~(f~(k~Nat -> j~Nat) -> n~Nat, n > 3), r~Nat, r > 3
    body (\k -> k)

fn by_name body -> r : body~(f~(k~Nat -> j~Nat) -> n~Nat, n > 3), r~Nat, r > 3
    body same

fn same k -> j : k~Nat, j~Nat
    k
