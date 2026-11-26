module type_eq_given_class

# A type equation on a class's type holds in the body: the elements are
# `U8`s, refinement included.

fn first_byte xs -> r : Seq s, Seq.Elem s == U8, xs~s, r~Option U8
    match xs
        []     -> None
        x :: _ -> Some x

fn total xs -> n : Seq s, Seq.Elem s == U8, xs~s, n~Nat
    match xs
        []        -> 0
        x :: rest -> x + total rest

fn below_256 xs -> r : Seq s, Seq.Elem s == U8, xs~s, r~Bool, r
    match xs
        []     -> True
        x :: _ -> x < 256
