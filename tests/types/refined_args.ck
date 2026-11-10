module refined_args

# D71: refinements inside type arguments are checked.
# Expected: an error on each line marked `error`, none elsewhere.

import list

type Small = n~Nat, n < 10

# Gaining a refinement where a value is built: an obligation (E0450).
fn lit -> xs : xs~List Small
    [1, 12]                                     # error: 12 < 10

fn cons_bad n xs -> ys : n~Nat, xs~List Small, ys~List Small
    n :: xs                                     # error: n < 10, counterexample n = 10

fn opt n -> o : n~Nat, o~Option Small
    Some n                                      # error: n < 10

fn tup n -> t : n~Nat, t~(Small, Nat)
    (n, n)                                      # error: n < 10 (first component only)

fn mapped xs -> ys : xs~List Small, ys~List Small
    list.map (\x -> x + 1) xs                   # error: x + 1 < 10, counterexample x = 9

# Forgetting a refinement is free (covariance)...
fn forget xs -> ys : xs~List Small, ys~List Nat
    xs

# Fine: the refinement is established, or assumed from a type.
fn cons_ok n xs -> ys : n~Nat, xs~List Small, ys~List Small
    if n < 10 then n :: xs else xs

fn first xs -> r : xs~List Small, r~Nat, r < 10
    match xs
        []     -> 0
        x :: _ -> x

fn halve xs -> ys : xs~List Small, ys~List Small
    list.map (\x -> x / 2) xs

# A function that needs a `Small` can't stand in for one that takes any `Nat`
# (contravariance): an obligation for any `Nat` (D85).
fn apply_nat f -> r : f~(Nat -> Nat), r~Nat
    f 20

fn pass_fn h -> r : h~(Small -> Nat), r~Nat
    apply_nat h                                 # error: n < 10, counterexample n = 10

fn pass_fn_ok h -> r : h~(Nat -> Small), r~Nat
    apply_nat h
