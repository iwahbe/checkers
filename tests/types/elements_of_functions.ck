# `list.all` and `list.map` promise `list.contains xs x`, which compares with
# `==`, also when the elements are functions: in a specification `==` is
# logical equality on any type.
module elements_of_functions

import std.list

fn all_positive fs -> r : fs~List (Int -> Int), r~Bool
    list.all (\f -> f 0 > 0) fs

fn at_zero fs -> r : fs~List (Int -> Int), r~List Int
    list.map (\f -> f 0) fs

check all_positive [\x -> x + 1, \x -> x * 2 + 1]
check at_zero [\x -> x + 1] == [1]
