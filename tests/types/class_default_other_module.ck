module class_default_other_module

# An instance of another module's class takes its type's default, which
# uses the class's parameter: here, at `Int`, `(Int, Tag)`.

import class_home.tagged (Tagged, Tag)

instance Tagged Int
    fn tag_of x
        (x, Tag 1)

fn entry -> e : e~(Int, Tag)
    Tagged.tag_of 5

check entry == (5, Tag 1)
