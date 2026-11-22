module class_post_match_type

# A postcondition matching on a result whose type mentions the class's
# type, at instances for a list, an array and a record, and in a generic
# recursive caller.

import std.array
import std.list (length)

class Seq s
    type Elem
    fn size xs -> n : xs~s, n~Nat
    fn uncons xs -> r : xs~s, r~Option (Elem, s),
                        match r
        None -> size xs == 0
        Some (_, rest) -> size rest < size xs

instance Seq (List a)
    type Elem = a
    fn size xs
        length xs
    fn uncons xs
        match xs
            []        -> None
            x :: rest -> Some (x, rest)

instance Seq (Array a)
    type Elem = a
    fn size xs
        len xs
    fn uncons xs
        if len xs == 0 then None else Some (xs[0], array.slice xs 1 (len xs))

record Countdown
    from~Nat

instance Seq Countdown
    type Elem = Nat
    fn size c
        c.from
    fn uncons c
        if c.from == 0 then None else Some (c.from, Countdown (c.from - 1))

fn count xs -> n : Seq s, xs~s, n~Nat
    decreasing Seq.size xs
    match Seq.uncons xs
        None           -> 0
        Some (_, rest) -> 1 + count rest

check count [1, 2, 3] == 3
check count (array.from_list [1, 2]) == 2
check count (Countdown 4) == 4
