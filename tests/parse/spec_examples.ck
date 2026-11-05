module spec_examples

# D0: the original example, in the decided syntax (D8).
fn foo x y -> z : x~Int, y~String
    format x + y

# §9.6 target for M3.
fn sort xs -> ys : xs~List Int, sorted ys, perm xs ys
    insertion_sort xs

# D10: generics by auto-binding.
fn map f xs -> ys : f~(a -> b), xs~List a
    match xs
        []      -> []
        x :: rs -> f x :: map f rs

# D19: '"' is a byte, "'" is a string.
check '"' == 34
check "'" ++ "s" == "'s"
