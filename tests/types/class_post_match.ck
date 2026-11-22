module class_post_match

# A class function's postcondition that is a `match` on its result: each
# instance proves it, and a generic caller has it after the call.

import std.list (length)

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
        if xs <= 0 then None else Some (xs - 1)

instance Peel (List a)
    fn size xs
        length xs
    fn peel xs
        match xs
            []        -> None
            _ :: rest -> Some rest

fn steps xs -> n : Peel s, xs~s, n~Nat
    decreasing Peel.size xs
    match Peel.peel xs
        None   -> 0
        Some y -> 1 + steps y

check steps 3 == 3
check steps [1, 2] == 2
