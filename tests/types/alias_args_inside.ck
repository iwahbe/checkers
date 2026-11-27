module alias_args_inside

# One refinement alias at different arguments is a different refinement:
# its predicates are compared with the arguments put in, wherever it is.
# An `Above 0` is not an `Above 10`, inside `Some` or passed to a
# function; an `Above 10` is an `Above 0`.

type Above lo = n~Int, n > lo

fn tighten x -> r : x~Above 0, r~Option (Above 10)
    Some x

fn tighten_inline x -> r : x~(n~Int, n > 0), r~Option (Above 10)
    Some x

fn need y -> r : y~Above 10, r~Int
    y

fn pass x -> r : x~Above 0, r~Int
    need x

fn loosen x -> r : x~Above 10, r~Option (Above 0)
    Some x

fn same x -> r : x~Above 10, r~Option (Above 10)
    Some x

fn tighten_deep x -> r : x~Above 0, r~Option (Option (Above 10))
    Some (Some x)

fn tighten_all xs -> r : xs~List (Above 0), r~List (Above 10)
    xs
