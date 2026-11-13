# bag.ck — finite multisets (D47, D138). The prover sees a `Bag a` as an
# array from values to counts, so facts about permutations need no quantifiers.
module std.bag

# A finite multiset of values of type `a`.
export abstract enum Bag a : a~Type

# The multiset of a list's elements.
export fn of xs -> b : xs~List a, b~Bag a
    __builtin

# How many times `x` occurs in `b`.
export fn count x b -> n : x~a, b~Bag a, n~Nat
    __builtin

# The union of two multisets: counts add up.
export fn sum a b -> c : a~Bag t, b~Bag t, c~Bag t
    __builtin
