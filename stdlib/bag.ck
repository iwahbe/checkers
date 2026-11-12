# bag.ck — finite multisets of integers (D47). The prover sees a `Bag` as an
# array from values to counts, so facts about permutations need no quantifiers.
module std.bag

# A finite multiset of integers.
export abstract enum Bag

# The multiset of a list's elements.
export fn of xs -> b : xs~List Int, b~Bag
    __builtin

# How many times `x` occurs in `b`.
export fn count x b -> n : x~Int, b~Bag, n~Nat
    __builtin

# The union of two multisets: counts add up.
export fn sum a b -> c : a~Bag, b~Bag, c~Bag
    __builtin
