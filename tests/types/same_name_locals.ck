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

# The number isn't one a local in scope has (`a1` here), nor a name in the
# message.
fn numbered a x -> r : a~Type, x~a, r~Int
    let f = \a a1 ->
        have x~Int
        0
    f Int Int

fn named a x -> r : a~Type, x~a, r~Int
    let f = \a a1 ->
        have x~a1
        0
    f Int Int
