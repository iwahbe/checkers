module class_type_refined

# A class's type at a known instance is the instance's type, its
# refinement kept: at `Array U8`, `Take.Item` is `U8`.

class Take s
    type Item
    fn take xs -> r : xs~s, r~Option Item

instance Take (Array a)
    type Item = a
    fn take xs
        if len xs == 0 then None else Some xs[0]

fn by_type x -> r : x~Take.Item (Array U8), r~U8
    x

fn by_match xs -> r : xs~Array U8, r~Option U8
    match take xs
        None   -> None
        Some x -> Some x

fn by_result xs -> r : xs~Array U8, r~Option U8
    take xs

# Not gained where the instance's type has no refinement.
fn by_match_int xs -> r : xs~Array Int, r~Option U8
    match take xs
        None   -> None
        Some x -> Some x

fn by_result_nat xs -> r : xs~Array Nat, r~Option U8
    take xs
