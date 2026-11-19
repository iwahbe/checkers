module refined_fn_generic_pre_named

import std.list

# A function type's precondition may call a generic function: its type
# argument is not a use of the named result, so the predicate is still a
# precondition, required of each call.
fn nonempty xs -> r : xs~List a, r~Bool
    match xs
        [] -> False
        _  -> True

fn by_empty f -> s : f~(i~List Int -> r~Int, nonempty i), s~Int
    f []

fn by_nonempty f -> s : f~(i~List Int -> r~Int, nonempty i), s~Int
    f [1]

fn by_std f -> s : f~(i~List Int -> r~Int, list.contains i 1), s~Int
    f [2]

fn by_std_met f -> s : f~(i~List Int -> r~Int, list.contains i 1), s~Int
    f [2, 1]

# A type argument nothing determines doesn't depend on the result either.
fn open_arg f -> s : f~(i~Int -> r~Int, nonempty []), s~Int
    f 0

# A predicate over the result is still a postcondition.
fn by_result f -> s : f~(i~Int -> r~List Int, nonempty r), s~Bool
    nonempty (f 0)
