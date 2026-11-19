module fn_value_unnamed_param

# A function whose precondition relates two parameters, passed where its
# parameters' types are unnamed: the message uses its own names.

fn pick n x -> r : n~Nat, x~Nat, x <= n, r~Nat
    x

fn use f -> r : f~(Nat -> Nat -> Nat), r~Nat
    f 1 2

fn main -> r : r~Nat
    use pick
