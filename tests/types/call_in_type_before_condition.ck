# A call in a type relies on every condition, wherever it is written:
# here, after the typing.
module call_in_type_before_condition

fn pos k -> r : k~Int, k > 0, r~Int
    k

record At n : n~ghost Int
    v~Int, v == n

fn in_result k -> r : k~Int, r~At (pos k), k > 0
    At (pos k)

# `a`'s refinement names `k`, a later parameter.
fn in_later_parameter a k : a~(x~Int, x < pos k), k~Int, k > 0
    ()

enum InConstructor
    InConstructor k a : k~Int, a~At (pos k), k > 0
