module class_qualified_before_proved

# A class's function named by its class (`C.f`) above the class, in a
# constant, a `check`, a type's refinement and another instance's function:
# known by its signature there, as below the class.

let FIVE = Make.make 5 + 0

check Make.make 5 == 5

type Small = n~Int, n < Make.make 9

fn small -> n : n~Small
    FIVE

instance Show Int
    fn show x -> s : x~Int, s~Int, s == x + 1
        x + Make.make 1

class Show a
    fn show x -> s : x~a, s~Int

class Make t
    fn make u -> r : u~Int, r~t

instance Make Int
    fn make u -> r : u~Int, r~Int, r == u
        u
