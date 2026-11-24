module class_type_clause

# A class's type may have class clauses (`type Item : Ord Item`): each
# instance's type must have them, and generic code uses them.

class Take s
    type Item : Ord Item
    fn take xs -> r : xs~s, r~Option Item

instance Take (List a) : Ord a
    type Item = a
    fn take xs
        match xs
            []     -> None
            x :: _ -> Some x

instance Take String
    type Item = Char
    fn take s
        match s
            []     -> None
            c :: _ -> Some c

# `<=` and `le` on `Take.Item s`: from `Take`'s dictionary.
fn by_operator xs ys -> r : Take s, xs~s, ys~s, r~Bool
    match (take xs, take ys)
        (Some x, Some y) -> x <= y
        _                -> False

fn by_function xs ys -> r : Take s, xs~s, ys~s, r~Bool
    match (take xs, take ys)
        (Some x, Some y) -> le x y
        _                -> False

# Passed on to a function with the clause `Ord a`.
fn larger x y -> r : Ord a, x~a, y~a, r~a
    if x <= y then y else x

fn by_clause xs ys -> r : Take s, xs~s, ys~s, r~Option (Take.Item s)
    match (take xs, take ys)
        (Some x, Some y) -> Some (larger x y)
        _                -> None

# A clause on a class's type in a signature is an ordinary clause.
fn by_signature xs -> r : Seq s, Add (Seq.Elem s), xs~s, r~Option (Seq.Elem s)
    match Seq.uncons xs
        None        -> None
        Some (x, _) -> Some (x + x)

check by_operator [1, 2] [3] == True
check by_operator "b" "a" == False
check by_clause "ab" "c" == Some 'c'
check by_signature [3, 4] == Some 6
