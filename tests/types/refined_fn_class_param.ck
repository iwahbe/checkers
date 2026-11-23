module refined_fn_class_param

# A lambda's parameter typed by a generic function's signature at a class's
# instance: its postcondition calls a class's function, so its refinement
# holds the instance's dictionary. Passed on, it promises what it says.
fn walk body xs -> r : Seq s, xs~s, body~(zs~s -> (self~(ys~s -> n~Nat, n <= Seq.size ys) -> m~Nat)), r~Nat
    body xs (\ys -> 0)

fn need_at_most self -> r : self~(ys~Bytes -> n~Nat, n <= Seq.size ys), r~Nat
    0

fn need_below self -> r : self~(ys~Bytes -> n~Nat, n < Seq.size ys), r~Nat
    0

fn by_at_most xs -> r : xs~Bytes, r~Nat
    walk (\zs self -> need_at_most self) xs

fn by_below xs -> r : xs~Bytes, r~Nat
    walk (\zs self -> need_below self) xs
