module type_eq_class_param

# A class's parameter fixed by a type equation counts as mentioned, and a
# use finds it from the other side.

enum Tok
    Plus
    Digit d : d~Nat

class Count a t
    fn count xs a -> r : Seq s, Seq.Elem s == t, xs~s, a~ghost Type, r~Nat

record Pluses
    seen~Nat

fn pluses xs -> r : Seq s, Seq.Elem s == Tok, xs~s, r~Nat
    match xs
        []           -> 0
        Plus :: rest -> 1 + pluses rest
        _ :: rest    -> pluses rest

instance Count Pluses Tok
    fn count xs a
        pluses xs

record Ones
    seen~Nat

fn ones xs -> r : Seq s, Seq.Elem s == Int, xs~s, r~Nat
    match xs
        []        -> 0
        x :: rest -> (if x == 1 then 1 else 0) + ones rest

instance Count Ones Int
    fn count xs a
        ones xs

check Count.count [Plus, Digit 1, Plus] Pluses == 2
check Count.count [1, 2, 1] Ones == 2

fn mixed -> r : r~Nat
    Count.count [1, 2] Pluses
