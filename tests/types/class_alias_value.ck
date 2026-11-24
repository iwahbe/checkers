module class_alias_value

# A class's function used at a refinement alias as a value: whether it
# gives the alias's values is checked where the value is called, with that
# call's facts, or against the function type it is passed as.

import std.list

class Make t
    fn make u -> r : u~Int, r~t

instance Make Int
    fn make u -> r : u~Int, r~Int, u >= 0 implies r >= 0
        u

fn by_let -> n : n~Nat
    let f = make
    f 5

fn by_map -> ns : ns~List Nat
    list.map make [1, 2]

fn by_map_negative -> ns : ns~List Nat
    list.map make [-1]

fn by_let_negative -> n : n~Nat
    let f = make
    f (-1)
