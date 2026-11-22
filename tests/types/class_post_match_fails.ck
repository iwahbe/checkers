module class_post_match_fails

# An instance whose function doesn't keep the class's postcondition, a
# `match` on its result.

class Peel s
    fn size xs -> n : xs~s, n~Nat
    fn peel xs -> r : xs~s, r~Option s,
                      match r
                          None   -> True
                          Some y -> size y < size xs

instance Peel Int
    fn size xs
        if xs < 0 then 0 else xs
    fn peel xs
        if xs <= 0 then None else Some xs
