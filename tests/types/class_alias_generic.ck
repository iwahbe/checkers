module class_alias_generic

# A dictionary at a refinement alias passed to generic code, which may call
# its functions with any arguments: each value of the class's type they
# return must be of the alias, for every argument.

class Make t
    fn make u -> r : u~Int, r~t

instance Make Int
    fn make u
        u

class Clamp t
    fn clamp u -> r : u~Int, r~t

instance Clamp Int
    fn clamp u -> r : u~Int, r~Int, r >= 0
        if u >= 0 then u else 0

fn made u -> r : Make t, u~Int, r~t
    make u

fn clamped u -> r : Clamp t, u~Int, r~t
    clamp u

fn by_clause -> n : n~Nat
    made 1

fn by_signature -> n : n~Nat
    clamped (-1)
