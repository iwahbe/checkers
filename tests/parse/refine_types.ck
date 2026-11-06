module refine_types

# D82: refinement types and refined function types inside types.
fn a xs f g -> r : xs~List (n~Int, n >= 5), f~(x~Int -> y~Int, x >= 5, y > x), g~(Int -> y~Int, y >= 0), r~Int
    0
