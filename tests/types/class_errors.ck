module class_errors

# What is wrong with a class or an instance, and with using them (D136).

class Show a
    fn show x -> s : x~a, s~String
    fn width x -> n : x~a, n
    lemma short x : x~a
        ensures len (show x) <= 80

record Name
    text~String

# Not a class.
instance Name Bool
    fn show b
        "?"

# Not for a type applied to variables.
instance Show (List Int)
    fn show xs
        "list"

# The class and the type are both the standard library's (the orphan rule).
instance Ord Int
    fn le x y
        x >= y

instance Show Name
    fn show n
        n.text
    fn width n
        len n.text
    lemma short m

# The same class and type again.
instance Show Name
    fn show n
        "name"
    fn width n
        0

instance Show Bool
    fn show b k
        "b"
    fn colour b
        "red"

# Missing a function.
instance Show (Option a)
    lemma short o

# A recursion through the class's function, which can't be checked.
enum Nest
    Leaf
    In n : n~Nest

instance Show Nest
    fn show n
        match n
            Leaf -> "leaf"
            In m -> Show.show m
    fn width n
        0

# Built by hand.
fn fake -> d : d~Ord Bool
    Ord (\x y -> True)

# No instance for a type parameter, nor for a function.
fn generic x -> r : x~a, r~Bool
    le x x

fn functions f -> r : f~(Int -> Int), r~Bool
    le f f

# The type isn't known.
fn unknown -> r : r~Bool
    le [] []

fn member x -> s : x~Name, s~String
    Show.print x
