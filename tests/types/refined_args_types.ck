module refined_args_types

# D71: refinements inside type arguments are checked.
# The type errors (E0262); the obligations are in refined_args.ck.
# Expected: an error on each line marked `error`, none elsewhere.

import cown (Cown)

type Small = n~Nat, n < 10

# Gaining a refinement through an existing value's type: a type error (E0262).
fn takes_small xs -> r : xs~List Small, r~Nat
    0

fn pass xs -> r : xs~List Nat, r~Nat
    takes_small xs                              # error: `List Nat` is not `List Small`

fn ret xs -> ys : xs~List Nat, ys~List Small
    xs                                          # error: `List Nat` is not `List Small`

fn nested xss -> r : xss~List (List Nat), r~Nat
    takes_nested xss                            # error: the inner `Nat`s aren't `Small`

fn takes_nested xss -> r : xss~List (List Small), r~Nat
    0

# Forgetting a refinement is free, except through a cown, which is invariant.
fn forget_cown c -> d : c~Cown Small, d~Cown Nat
    c                                           # error: `Cown Small` is not `Cown Nat`

