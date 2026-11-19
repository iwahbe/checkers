module refined_fn_generic_pre

# A function type's precondition may call a generic function: its type
# argument is not a use of the unnamed result.
fn nonempty xs -> r : xs~List a, r~Bool
    match xs
        [] -> False
        _  -> True

fn takes f -> s : f~(i~List Int -> Int, nonempty i), s~Int
    0

fn by_empty f -> s : f~(i~List Int -> Int, nonempty i), s~Int
    f []

fn by_nonempty f -> s : f~(i~List Int -> Int, nonempty i), s~Int
    f [1]
