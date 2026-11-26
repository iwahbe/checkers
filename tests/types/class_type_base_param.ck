module class_type_base_param

import std.list (length)

# A base type may name the class's parameter: at each instance it is the
# instance's type.

class Wrap s
    type Part : p~List s
    fn part x -> p : x~s, p~Part

instance Wrap Int
    type Part = List Int
    fn part x
        [x]

instance Wrap Bool
    type Part = List Int
    fn part x
        []

fn count x -> n : Wrap s, x~s, n~Nat
    length (part x)
