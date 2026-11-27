# A call in a type relies on the conditions written before its typing:
# a function's result and parameters, a record's fields, a constructor's.
module call_in_type_after_condition

fn pos k -> r : k~Int, k > 0, r~Int
    k

record At n : n~ghost Int
    v~Int, v == n

fn in_result k -> r : k~Int, k > 0, r~At (pos k)
    At (pos k)

# `n` is bound by `b`'s type.
fn auto_bound b k -> r : b~At n, k~Int, k > 0, r~At (pos k)
    At (pos k)

fn in_parameter k a : k~Int, k > 0, a~At (pos k)
    ()

record InField
    k~Int, k > 0
    a~At (pos k)

enum InConstructor
    InConstructor k a : k~Int, k > 0, a~At (pos k)
