# A constructor in a pattern is one of the type of the value it matches,
# whether or not that type, or the constructor, is imported: at the top of
# the pattern and inside it.
module constructor_from_type

import ctor_home.kinds (wrapped)

fn nested -> r : r~Int
    match wrapped
        Wrap A -> 0
        Wrap B -> 1
        Empty  -> 2

check nested == 1

fn unknown -> r : r~Int
    match wrapped
        Wrap C -> 0
        _      -> 1
