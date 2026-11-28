module spec_examples

# #494: the original example, in the decided syntax (#502).
fn foo x y -> z : x~Int, y~String
    format x + y

# §9.6 target for M3.
fn sort xs -> ys : xs~List Int, sorted ys, perm xs ys
    insertion_sort xs

# #504: generics by auto-binding.
fn map f xs -> ys : f~(a -> b), xs~List a
    match xs
        []      -> []
        x :: rs -> f x :: map f rs

# #509: '"' is a byte, "'" is a string.
check '"' == 34
check "'" ++ "s" == "'s"
