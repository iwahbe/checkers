module class_type_clause_errors

# A class's type's clauses are checked at each instance, and are its only
# ones in generic code.

class Take s
    type Item : Ord Item
    fn take xs -> r : xs~s, r~Option Item

record Point
    x~Int

record Box
    item~Point

# `Point` has no instance of `Ord`.
instance Take Box
    type Item = Point
    fn take b
        Some b.item

# `List a` without the context `Ord a`.
instance Take (List a)
    type Item = a
    fn take xs
        match xs
            []     -> None
            x :: _ -> Some x

# Only `Ord`: no `+`.
fn twice xs -> r : Take s, xs~s, r~Option (Take.Item s)
    match take xs
        None   -> None
        Some x -> Some (x + x)

# A clause names the class's type itself.
class Bad s
    type Item : Ord s
    type Other : x~s
    type Third : x~Item, y~Item
    fn pick xs -> r : xs~s, r~Item
