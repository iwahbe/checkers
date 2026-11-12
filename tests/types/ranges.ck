# Arithmetic keeps constant bounds (D135): the result's type is the range
# the operands' bounds give, so what flows through inferred types keeps it.
module ranges

import std.list

# `x + 1` is in `1 … 256`, so the mapped list's elements are too: proven.
fn bounded xs -> r : xs~List U8, r~Bool, r == True
    let ys = list.map (\x -> x + 1) xs
    match ys
        y :: _ -> y <= 256
        []     -> True

# The branches of an inferred `if` join: `y` is in `0 … 300`.
fn joined b x -> r : b~Bool, x~U8, r~Nat, r <= 300
    let y = if b then x else 300
    y

# Euclidean `%` by a constant: `0 … 15`. `-` of `Nat`s keeps its obligation.
fn low x -> r : x~U32, r~U8
    let m = x % 16
    m

fn down x -> r : x~U8, r~Nat, r <= 254
    if x >= 1 then x - 1 else 0

# A bound that isn't a constant is dropped: `i + 1` is only `1 <= n`.
fn next src i -> r : src~Bytes, i~Nat, i < len src, r~Nat, r <= len src
    let j = i + 1
    j

# Still wrong where the range says so: `x + 1` reaches 256.
fn wrong x -> r : x~U8, r~U8
    let y = x + 1
    y

# What it is, in a message.
fn shown x -> r : x~U8, r~String
    let y = x * 2
    y

# Each operand's range is its own: `y` is a `U32`, not a `U8`, so the sum
# can pass 510.
fn mixed x y -> r : x~U8, y~U32, r~Nat, r <= 510
    let s = x + y
    s

# A range isn't imposed on what it is compared with: `e` is a `Nat`.
fn compared q e -> r : q~U8, q + 1 < e, r~Nat
    e
