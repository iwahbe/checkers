module stray_typing

# A typing of a name that isn't the declaration's is an error, and its
# type is still resolved.

record Box : missing~UnknownA
    value~Int

enum Choice : missing~UnknownB
    Choice

fn walk x -> r : x~Int, missing~UnknownC, r~Int
    x

lemma by_refl x : x~Int, missing~UnknownD
    ensures x == x

enum Pair
    Pair a : a~Int, missing~UnknownE
