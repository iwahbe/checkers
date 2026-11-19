# A lemma's induction may follow a measure, as a function's recursion
# does: written with `decreasing`, or guessed.
module lemma_measure

fn walk n x -> r : n~Nat, x~Nat, x <= n, r~Nat
    if x < n then walk n (x + 1) else x

# The measure written.
lemma by_measure n x : n~Nat, x~Nat, x <= n
    ensures walk n x == n
    proof
        decreasing n - x
        if x < n then have by_measure n (x + 1) else auto

# The measure guessed from the guard `x < n`.
lemma by_guess n x : n~Nat, x~Nat, x <= n
    ensures walk n x == n
    proof
        if x < n then have by_guess n (x + 1) else auto

# A measure the induction doesn't make smaller.
lemma not_smaller n x : n~Nat, x~Nat, x <= n
    ensures walk n x == n
    proof
        decreasing x
        if x < n then have not_smaller n (x + 1) else auto

# No measure the guess tries is made smaller.
lemma no_guess x : x~Int
    ensures x > x
    proof
        have no_guess (x + 1)

# The measure may use the lemma's `let`s.
lemma by_let n x : n~Nat, x~Nat, x <= n
    let left = n - x
    ensures walk n x == n
    proof
        decreasing left
        if x < n then have by_let n (x + 1) else auto

# An instance's lemma gives its measure in its proof.
class Walker a
    fn steps w n x -> r : w~a, n~Nat, x~Nat, r~Nat
    lemma steps_end w n x : w~a, n~Nat, x~Nat, x <= n
        ensures steps w n x == n

record Unit
    u~Int

instance Walker Unit
    fn steps w n x
        if x < n then steps w n (x + 1) else x
    lemma steps_end w n x
        proof
            decreasing n - x
            if x < n then have steps_end w n (x + 1) else auto

# A measure there is checked as in any lemma.
record Other
    o~Int

instance Walker Other
    fn steps w n x
        if x < n then steps w n (x + 1) else x
    lemma steps_end w n x
        proof
            decreasing x
            if x < n then have steps_end w n (x + 1) else auto
