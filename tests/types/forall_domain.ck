module forall_domain

# A `forall`'s variables range over their types, where it is proved and
# where it is a premise: a `Nat` is non-negative, a refinement's predicates
# hold.

# A premise over `Nat` says nothing of negative values.
lemma from_nat f : f~(Int -> Bool), all: forall k : k~Nat, f k
    ensures forall k : k~Int, f k

# Nor one over a refinement of values outside it.
lemma from_range f : f~(Int -> Bool), all: forall k : k~(k~Int, k < 0), f k
    ensures forall k : k~Int, f k

# Every `Nat` is non-negative.
lemma nat_goal
    ensures forall k : k~Nat, k >= 0

# Every value of a refinement satisfies it.
lemma ref_goal
    ensures forall k : k~(k~Int, k >= 0, k < 2), k < 2

fn needs_nat f -> r : f~(Int -> Bool), all: forall k : k~Nat, f k, r~Bool
    True

# A premise over a narrower type does not meet a precondition over `Nat`.
fn from_narrower f -> r : f~(Int -> Bool), all: forall k : k~(k~Int, k >= 1), f k, r~Bool
    needs_nat f

# One over a wider type does.
fn from_wider f -> r : f~(Int -> Bool), all: forall k : k~Int, f k, r~Bool
    needs_nat f
