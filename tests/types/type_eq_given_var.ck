module type_eq_given_var

# A function's own type equation on a type parameter holds in its body,
# and each call must meet it.

fn zero t -> r : t~ghost Type, t == Int, r~t
    0

check zero Int == 0

fn not_bool -> r : r~Bool
    zero Bool
