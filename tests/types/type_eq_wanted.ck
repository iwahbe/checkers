module type_eq_wanted

import std.array

# Each use must meet the type equation: an unknown is solved by it, and a
# type that doesn't meet it is refused.

fn first_byte xs -> r : Seq s, Seq.Elem s == U8, xs~s, r~Option U8
    match xs
        []     -> None
        x :: _ -> Some x

check first_byte b"\x07" == Some 7
check first_byte (array.to_list b"\x07") == Some 7
check first_byte [] == None

fn from_text s -> r : s~String, r~Option U8
    first_byte s

fn from_ints xs -> r : xs~List Int, r~Option U8
    first_byte xs
