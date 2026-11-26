# A name that is a constructor of the type of the value matched means that
# constructor (proposed), even where a constructor of another type by that
# name is in scope. It imports `tests/types/ctor_home/kinds.ck`.
module constructor_from_type_first

import ctor_home.kinds (Inner, B)

enum Other
    A

fn first i -> r : i~Inner, r~Int
    match i
        A -> 0
        B -> 1

check first B == 1
