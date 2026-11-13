# Classes over type constructors (M25, D136): `Functor`'s lemmas proved
# for each instance, used at a type parameter, and the errors.
module functor

import std.array

record Box a
    item~a

# Proved: `fmap_id` and `fmap_comp` with Box's `fmap` in place of the class's.
instance Functor Box
    fn fmap g b
        Box (g b.item)

# For a type constructor short of its last parameter: `Pair k` holds a
# `k` and an element.
record Pair k v
    key~k
    val~v

instance Functor (Pair k)
    fn fmap g p
        Pair p.key (g p.val)

lemma keeps_key p : p~Pair String Int
    ensures (fmap (\x -> x + 1) p).key == p.key

# An instance whose lemmas don't hold: it drops the elements.
enum Bad a : a~Type
    Empty
    Full x : x~a

instance Functor Bad
    fn fmap g b
        Empty

# At any `Functor`, `fmap` is a function Z3 knows nothing about except
# through the lemmas brought in with `have`.
lemma comp_twice xs : Functor f, xs~f Int
    ensures fmap (\x -> x + 1) (fmap (\x -> x * 2) xs) == fmap (\x -> 2 * x + 1) xs
    proof
        have Functor.fmap_comp (\x -> x + 1) (\x -> x * 2) xs

lemma id_any xs : Functor f, xs~f String
    ensures fmap (\s -> s) xs == xs
    proof
        have Functor.fmap_id xs

# Not without the lemma.
lemma no_lemma xs : Functor f, xs~f Int
    ensures fmap (\x -> x) xs == xs

# Not true of every `Functor`.
lemma not_every xs : Functor f, xs~f Int
    ensures fmap (\x -> x + 1) xs == xs

# Known instances are their bodies.
lemma at_list xs : xs~List Int
    ensures fmap (\x -> x) (1 :: xs) == 1 :: fmap (\x -> x) xs

lemma at_array xs : xs~Array Int
    ensures fmap (\x -> x * 3) xs == array.map (\x -> x * 3) xs

# `Functor` is for type constructors, not types.
instance Functor Int
    fn fmap g x
        x

# Nor for a type constructor still short of a parameter.
instance Ord List
    fn le xs ys
        True

fn wrong x -> r : x~Int, r~Int
    fmap (\y -> y) x

# A type constructor parameter promises nothing about its argument, so a
# recursive type may not be one (an instance like `record Neg a : run~(a -> Int)`
# would make the logic inconsistent).
enum Rose f a : f~(Type -> Type), a~Type
    Node x kids : x~a, kids~f (Rose f a)

# Through a known type that holds only values of it, it may.
enum Tree a : a~Type
    Leaf
    Branch x kids : x~a, kids~List (Tree a)

# A type parameter of kind `Type -> Type` is found from how it is applied.
fn size xs -> n : xs~f Int, n~Int
    0

check size [1, 2] == 0
check size (Some 1) == 0
