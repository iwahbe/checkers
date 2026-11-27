module refined_alias_chain

# A refinement is found behind any number of aliases: `Int` inside
# `Option` is not the `Nat` that `A33` stands for.

type A0 = x~Nat
type A1 = x~A0
type A2 = x~A1
type A3 = x~A2
type A4 = x~A3
type A5 = x~A4
type A6 = x~A5
type A7 = x~A6
type A8 = x~A7
type A9 = x~A8
type A10 = x~A9
type A11 = x~A10
type A12 = x~A11
type A13 = x~A12
type A14 = x~A13
type A15 = x~A14
type A16 = x~A15
type A17 = x~A16
type A18 = x~A17
type A19 = x~A18
type A20 = x~A19
type A21 = x~A20
type A22 = x~A21
type A23 = x~A22
type A24 = x~A23
type A25 = x~A24
type A26 = x~A25
type A27 = x~A26
type A28 = x~A27
type A29 = x~A28
type A30 = x~A29
type A31 = x~A30
type A32 = x~A31
type A33 = x~A32

fn gain x -> r : x~Option Int, r~Option A33
    x
