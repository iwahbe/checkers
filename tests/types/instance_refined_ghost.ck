module instance_refined_ghost

# A member taking the class's parameters explicitly (`a~ghost Type`,
# `t~ghost Type`), with class clauses of its own: the instance's signature
# takes them too, and a known call gets the instance's postcondition.

import std.parse (Parsable, Token, consumed)

record One
    v~Int

enum OneError
    Empty

instance Parsable One Int
    type Error = OneError
    fn parse xs a t -> r : Seq s, Token (Seq.Elem s) t, xs~s, a~ghost Type, t~ghost Type,
                           r~Result (One, s) Error, consumed r xs,
                           match r
                               Ok (o, _) -> o.v == 1
                               Err _     -> True
        match xs
            _ :: rest -> Ok (One 1, rest)
            []        -> Err Empty

fn first xs -> r : xs~List Int, r~Bool, r
    match Parsable.parse xs One Int
        Ok (o, _) -> o.v == 1
        Err _     -> True
