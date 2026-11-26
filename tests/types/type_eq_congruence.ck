module type_eq_congruence

# Type equations combine, and reach inside other types.

fn first xs -> r : Seq s, Seq.Elem s == t, t == U8, xs~s, r~Option (t, s)
    Seq.uncons xs

fn as_byte xs -> r : Seq s, Seq.Elem s == t, t == U8, xs~s, r~Option U8
    match first xs
        None        -> None
        Some (x, _) -> Some x
