module own_type

# `own (a -> b)` is the type of a function to call exactly once, written
# anywhere a type is. A function that may be called any number of times is
# one too. `own` on a type that isn't a function type means nothing.

fn not_a_function x : x~Option (own Int)
    ()

fn held o -> r : o~Option (own (Unit -> Unit)), r~Unit
    match o
        Some k -> k ()
        None   -> ()

fn given_any -> r : r~Unit
    held (Some (\_ -> ()))
