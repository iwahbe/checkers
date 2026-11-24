module class_alias_proved

# A class used at a refinement alias, where the instance's signature shows
# its values are of the alias: a result promised non-negative, a class
# whose functions return none of its type (`Ord`), and a class's type.

class Make t
    type Out
    fn make u -> r : u~Int, r~t

instance Make Int
    type Out = Bool
    fn make u -> r : u~Int, r~Int, r >= 0
        if u >= 0 then u else 0

fn direct -> n : n~Nat
    make (-1)

fn generic u -> r : Make t, u~Int, r~t
    make u

fn by_clause -> n : n~Nat
    generic 7

fn out b -> c : b~Make.Out Nat, c~Bool
    b

fn larger x y -> r : Ord a, x~a, y~a, r~a
    if x <= y then y else x

fn biggest x y -> n : x~Nat, y~Nat, n~Nat
    larger x y
