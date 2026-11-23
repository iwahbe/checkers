# A function parameter's precondition that calls a class's function and
# mentions a later parameter (`Seq.size ys < Seq.size xs`).
module later_param_class_precondition

# The postcondition doesn't follow: `f` may return `xs`.
fn wrong f xs -> r : f~(ys~List Int -> List Int, Seq.size ys < Seq.size xs), xs~List Int, r~List Int, r != xs
    match xs
        []     -> [0]
        _ :: t -> f t

# A lambda given where such a function is expected has the precondition as a
# fact: `Seq.size xs - Seq.size ys` is a `Nat`.
fn by_lambda body xs -> r : Seq s, body~(f~(ys~s -> n~Nat, Seq.size ys < Seq.size xs) -> m~Nat), xs~s, r~Nat
    body (\ys -> Seq.size xs - Seq.size ys)

# Passed on as it is.
fn passed body xs -> r : Seq s, body~(f~(ys~s -> n~Nat, Seq.size ys < Seq.size xs) -> m~Nat), xs~s, r~Nat
    by_lambda body xs
