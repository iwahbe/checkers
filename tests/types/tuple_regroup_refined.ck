module tuple_regroup_refined

# `(a, (b, c))` is `(a, b, c)`: regrouping a tuple's parts keeps each part's
# refinement to check, as for tuples grouped alike.

fn nested xs -> r : xs~List (Int, (Int, Int)), r~List (Int, Nat, Int)
    xs                                          # error E0262

fn flat xs -> r : xs~List (Int, Int, Int), r~List (Int, Nat, Int)
    xs                                          # error E0262

fn to_nested xs -> r : xs~List (Int, Int, Int), r~List (Int, (Nat, Int))
    xs                                          # error E0262

fn last xs -> r : xs~List (Int, (Int, Int)), r~List (Int, Int, Nat)
    xs                                          # error E0262

# Regrouping alone gains nothing: accepted.
fn keeps xs -> r : xs~List (Int, (Nat, Int)), r~List (Int, Nat, Int)
    xs

fn drops xs -> r : xs~List (Nat, Nat, Int), r~List (Int, (Int, Int))
    xs

# A last part that is a refinement of a tuple stays whole: the other side's
# rest is checked against it.
fn first p -> r : p~(Int, Int), r~Int
    let (a, _) = p
    a

fn second p -> r : p~(Int, Int), r~Int
    let (_, b) = p
    b

type Ordered = p~(Int, Int), first p <= second p

fn rest xs -> r : xs~List (Int, Int, Int), r~List (Int, Ordered)
    xs                                          # error E0262

fn rest_kept xs -> r : xs~List (Nat, Ordered), r~List (Int, Int, Int)
    xs
