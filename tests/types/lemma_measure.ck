# A lemma's induction may follow a measure, as a function's recursion
# does: written with `decreasing`, or guessed.
module lemma_measure

fn walk n x -> r : n~Nat, x~Nat, x <= n, r~Nat
    if x < n then walk n (x + 1) else x

# The measure written.
lemma by_measure n x : n~Nat, x~Nat, x <= n
    decreasing n - x
    ensures walk n x == n
    proof
        if x < n then have by_measure n (x + 1) else auto

# The measure guessed from the guard `x < n`.
lemma by_guess n x : n~Nat, x~Nat, x <= n
    ensures walk n x == n
    proof
        if x < n then have by_guess n (x + 1) else auto

# A measure the induction doesn't make smaller.
lemma not_smaller n x : n~Nat, x~Nat, x <= n
    decreasing x
    ensures walk n x == n
    proof
        if x < n then have not_smaller n (x + 1) else auto

# No measure the guess tries is made smaller.
lemma no_guess x : x~Int
    ensures x > x
    proof
        have no_guess (x + 1)
