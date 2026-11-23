module class_alias_result

# A class used at a refinement alias runs the instance of the type the
# alias stands for: `make` at `Nat` runs `Int`'s, whose signature doesn't
# say its result is non-negative.

class Make t
    fn make u -> r : u~Int, r~t

instance Make Int
    fn make u
        u

fn wrong -> n : n~Nat
    make (-1)
