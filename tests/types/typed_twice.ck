module typed_twice

# Several typings of one name combine: each refines its type, in any order,
# as a predicate would.

fn refined x -> r : x~Int, x~(n~Int, n > 0), r~Int
    x

check refined 1 == 1
check refined 0 == 0

fn reversed x -> r : x~(n~Int, n > 0), x~Int, r~Int
    x

check reversed 0 == 0

fn need_nat n -> r : n~Nat, r~Nat
    n

fn in_body x -> r : x~Int, x~Nat, r~Nat
    need_nat x

fn result x -> r : x~Int, r~Int, r~Nat
    x

lemma stated x : x~Int, x~Nat
    ensures x >= 0

enum Shape
    Square side : side~Int, side~Nat

fn negative -> r : r~Shape
    Square (-1)

class Pick a
    fn pick w -> r : w~a, r~Int, r~Nat

instance Pick Bool
    fn pick w
        -1

instance Pick Unit
    fn pick w -> r : w~Unit, r~Int, r~Nat
        -1

instance Pick Int
    fn pick w -> r : w~Int, r~Int
        0
