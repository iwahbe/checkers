# A specification mustn't speak of a call that can't be made (D118): a call
# in a precondition, postcondition or `ensures` needs its callee's
# precondition, which may come from the conditions before it.
module spec_preconditions

fn half x -> r : x~Nat, x >= 1, r~Nat
    decreasing x
    if x == 1 then 0 else 1 + half (x / 2)

# Fine: `x >= 1` comes first.
fn halved x -> r : x~Nat, x >= 1, r~Nat, r == half x
    half x

# E0450: nothing says `x >= 1`.
fn unguarded x -> r : x~Nat, r~Nat, r == half x
    0

# Fine: the hypothesis gives `y >= 1`.
lemma half_two y : y~Nat, y == 2
    ensures half y == 1
    proof
        auto

# E0450: `half 0` is no value at all; once, though the conclusion is elaborated twice.
lemma half_zero y : y~Nat, y == 0
    ensures half y == half y
    proof
        auto
