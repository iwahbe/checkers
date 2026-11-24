module class_type_shown

fn by_literal xs -> r : Seq s, xs~s, r~Bool
    match xs
        []     -> False
        x :: _ -> x == 1

fn by_result xs -> r : Seq s, xs~s, r~Option Int
    match xs
        []     -> None
        x :: _ -> Some x

fn by_refinement xs -> r : xs~Array U8, r~Option (U8, Array U8)
    Seq.uncons xs
