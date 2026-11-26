module type_eq_deferred

# A type equation that can't be decided yet waits for the type.

fn first_byte xs -> r : Seq s, Seq.Elem s == U8, xs~s, r~Option U8
    match xs
        []     -> None
        x :: _ -> Some x

fn apply f xs -> r : f~(s -> Option U8), xs~s, r~Option U8
    f xs

check apply first_byte b"\x01" == Some 1
