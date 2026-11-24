module typed_twice

# A name is given one type. A second one is an error, not ignored: its
# refinement would otherwise go unchecked, and its names are still resolved.

fn refined x -> r : x~Int, x~(n~Int, n > 0), r~Int
    x

fn result x -> r : x~Int, r~Int, r~Bool
    x

fn unknown x : x~Int, x~Missing
    x

lemma stated x : x~Int, x~Nat
    ensures x == x

enum Shape
    Square side : side~Int, side~Nat

record Pair a : a~Type, a~Type
    left~a

class Pick a
    fn pick w -> r : w~a, w~a, r~Int

instance Pick Bool
    fn pick w -> r : w~Bool, r~Int, r~Nat
        0
