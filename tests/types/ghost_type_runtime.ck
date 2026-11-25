module ghost_type_runtime

fn keep t -> n : t~Type, n~Nat
    0

fn erased x t -> n : x~Nat, t~ghost Type, n~Nat
    x

# Passed where it is erased: not a use at run time.
fn by_ghost xs -> n : xs~List a, n~Nat
    erased 1 a

# Passed to a parameter that isn't `ghost`: a use at run time.
fn by_value xs -> n : xs~List a, n~Nat
    let _ = erased 1 a
    keep a

class Make t
    fn make x t -> n : x~Nat, t~ghost Type, n~Nat

# The class's parameter is `ghost` in an instance's function too.
instance Make Bool
    fn make x t
        keep t
