# A local hidden by another of its name is shown numbered, and a note says
# where each is bound: beside the one that hides it, and alone.
module same_name_locals

fn hidden a x -> r : a~Type, x~a, r~Int
    let f = \a ->
        have x~a
        0
    f Int

fn alone a x -> r : a~Type, x~a, r~Int
    let f = \a ->
        have x~Int
        0
    f Int
