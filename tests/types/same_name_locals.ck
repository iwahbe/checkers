# Two locals of the same name, one hiding the other: the hidden one is
# shown numbered, and a note says where each is bound.
module same_name_locals

fn hidden a x -> r : a~Type, x~a, r~Int
    let f = \a ->
        have x~a
        0
    f Int
