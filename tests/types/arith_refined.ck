# Arithmetic on a refinement gives its base number type (D134): `x + 1`
# for an `I8` `x` is an `Int`, an `I8` only where checked against `I8`.
# Before D134 the sum was typed `I8` unchecked, so `h` proved `r == 0`
# though `h [127]` is 1.
module arith_refined

import std.list

fn h xs -> r : xs~List I8, r~Nat, r == 0
    let ys = list.map (\x -> x + 1) xs
    match ys
        y :: _ -> if y < 128 then 0 else 1
        []     -> 0

# Checked against `I8`, the sum must be proven one: E0450.
fn g xs -> r : xs~List I8, r~List I8
    list.map (\x -> x + 1) xs

# `Nat`s stay `Nat`s (D121 c), and so do sums of `U8`s.
fn n a b -> r : a~U8, b~U8, r~Nat
    a + b

check h [127] == 1
