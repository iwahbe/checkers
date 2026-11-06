module refined_fn_types

# M10 (D82–D87): refined types inside types, refined function types,
# refinements compared by implication, partial applications everywhere.
# The E0262 case is in refined_fn_gain.ck (no proving once a file has a
# type error).

import list

type Big = n~Int, n >= 5

fn at_least k x -> y : k~Int, x~Int, x >= k, y~Int, y >= 0
    x - k

fn sub5 x -> y : x~Big, y~Int, y >= 0
    x - 5

# ── checks with no errors ───────────────────────────────────────────────────

# D82 + D86: the done-when of M10.
fn shift xs -> ys : xs~List (n~Int, n >= 5), ys~List (m~Int, m >= 0)
    list.map (at_least 5) xs

# D87: `xs` types `map`'s `a` before `sub5` is checked against `(a -> b)`.
fn shift_named xs -> ys : xs~List Big, ys~List Int
    list.map sub5 xs

# D83: an alias and an inline refinement with the same predicate are one type.
fn same xs -> ys : xs~List Big, ys~List (n~Int, n >= 5)
    xs

# D83: a stronger refinement passes as a weaker one (n >= 6 ⇒ n >= 5).
fn weaken xs -> ys : xs~List (n~Int, n >= 6), ys~List Big
    xs

# D84: the result of a call is known to satisfy the postcondition.
fn apply f x -> r : f~(x~Int -> y~Int, x >= 5, y >= 0), x~Big, r~Int, r >= 0
    f x

# D85: passing a function that needs less and promises more is fine.
fn pass_ok -> r : r~Int, r >= 0
    apply (at_least 3) 7

# D85: a lambda is checked with the precondition as a fact.
fn pass_lambda -> r : r~Int, r >= 0
    apply (\x -> x - 5) 9

# ── errors ──────────────────────────────────────────────────────────────────

# D85: `at_least 7` needs more than `map` promises (it may get any `Big`).
fn too_strict xs -> ys : xs~List Big, ys~List Int
    list.map (at_least 7) xs                    # error E0450: needs `x >= 7`, counterexample x = 5

# D84: the call's argument doesn't meet the precondition.
fn bad_call f -> r : f~(x~Int -> y~Int, x >= 5, y >= 0), r~Int
    f 3                                         # error E0450: `x >= 5`, required to call `f`

# D85: a lambda whose result doesn't meet the postcondition.
fn bad_lambda -> r : r~Int, r >= 0
    apply (\x -> x - 9) 9                       # error E0450: `y >= 0` of `x - 9`, counterexample x = 5

# D83: a weaker refinement can't pass as a stronger one.
fn strengthen xs -> ys : xs~List Big, ys~List (n~Int, n >= 6)
    xs                                          # error E0450: every `Big` is `n >= 6`, counterexample n = 5
