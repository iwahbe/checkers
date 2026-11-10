module prove

# The prover's contract (SPEC §7): each kind of obligation, proved and not.

import list (length)

record Range
    lo~Nat
    hi~Nat, lo <= hi

# ── proved ───────────────────────────────────────────────────────────────────

fn width r -> n : r~Range, n~Nat
    r.hi - r.lo                       # the invariant lo <= hi makes this safe

fn clamp lo hi x -> y : lo~Int, hi~Int, x~Int, lo <= hi, y~Int, lo <= y, y <= hi
    if x < lo then lo else if x > hi then hi else x

fn mid a b -> m : a~Nat, b~Nat, a <= b, m~Nat, a <= m, m <= b
    a + (b - a) / 2

fn make lo hi -> r : lo~Nat, hi~Nat, r~Range
    if lo <= hi then Range lo hi else Range hi lo

fn safe_div a b -> q : a~Int, b~Int, q~Int
    if b == 0 then 0 else a / b

fn byte_at src i -> b : src~Bytes, i~Nat, b~Nat
    if i < len src then src[i] else 0

fn small n -> b : n~U8, b~Bool
    n < 300

# Induction: the recursive `have` is the induction hypothesis (D49).
lemma length_append xs ys : xs~List Int, ys~List Int
    ensures length (xs ++ ys) == length xs + length ys
    proof
        match xs
            []        -> auto
            _ :: rest -> have length_append rest ys

fn uses_lemma xs ys -> n : xs~List Int, ys~List Int, n~Nat, n >= length xs
    have length_append xs ys
    length (xs ++ ys)

fn checked x -> y : x~Int, y~Int, y >= 0
    have x * x >= 0
    x * x

# ── not proved ───────────────────────────────────────────────────────────────

fn bad_width r -> n : r~Range, n~Nat
    r.lo - r.hi

fn bad_clamp lo hi x -> y : lo~Int, hi~Int, x~Int, y~Int, lo <= y
    if x < lo then lo else x - 1

fn bad_make lo hi -> r : lo~Nat, hi~Nat, r~Range
    Range lo hi

fn bad_div a b -> q : a~Int, b~Int, q~Int
    a / b

fn bad_index src -> b : src~Bytes, b~Nat
    src[0]

fn bad_call -> m : m~Nat
    mid 3 1

lemma no_proof x : x~Int
    ensures x + 1 > x

lemma false_lemma x : x~Int
    ensures x > 0

lemma trusted_lemma x : x~Int
    ensures x > 0
    proof
        admit

# A lambda that captures a local is outside the fragment (a closed one is
# specialized, see higher_order.ck).
fn outside xs k -> n : xs~List Int, k~Int, n~Nat, n == length (list.map (\x -> x + k) xs)
    length xs
