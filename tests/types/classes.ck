module classes

# Classes and instances (D136): a class lists the functions and lemmas each
# instance gives; generic code uses them through a clause `C a`.

class Size a
    fn size x -> n : x~a, n~Nat
    # Nothing is smaller than its parts' sizes put together: here, just
    # that a size is a size.
    lemma small x : x~a
        ensures size x >= 0

instance Size Bool
    fn size b
        if b then 1 else 0

record Pair a b
    first~a
    second~b

# Inside an instance, `size` is this instance's own; the class's function
# at another type is `Size.size`.
instance Size (Pair a b) : Size a, Size b
    fn size p
        Size.size p.first + Size.size p.second

enum Tree a
    Leaf
    Node l x r : l~Tree a, x~a, r~Tree a

# An instance needing its own functions: recursion on the tree itself.
instance Size (Tree a) : Size a
    fn size t
        match t
            Leaf       -> 0
            Node l x r -> size l + Size.size x + size r

# Generic code: the clause makes `size` available at `a`.
fn total xs -> n : Size a, xs~List a, n~Nat
    match xs
        []        -> 0
        x :: rest -> size x + total rest

# Two classes, and a class's function named through the class.
instance Ord Bool2
    fn le x y
        not x.b or y.b

record Bool2
    b~Bool

fn both x -> n : Size a, Ord a, x~a, n~Nat, n == Size.size x
    have refl x
    if le x x then size x else 0

# A class's lemma, used at a type parameter.
fn at_least x -> r : Ord a, x~a, r~Bool, r
    have refl x
    Ord.le x x

check total [True, False, True] == 2
check size (Pair True (Pair False True)) == 2
check size (Node Leaf True (Node Leaf True Leaf)) == 2
check both True == 1
check at_least "x"
