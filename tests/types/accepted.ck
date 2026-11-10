module accepted

# Everything in this file must type-check with no diagnostics.

import std.list (map, length, reverse)

enum Shape
    Circle r : r~Nat
    Rect w h : w~Nat, h~Nat

record Point
    x~Int
    y~Int

# Parameterised record whose field types depend on a value parameter.
record Bounded limit : limit~Nat
    value~Nat, value <= limit

enum Vec a n : a~Type, n~Nat
    VNil       : n == 0
    VCons x xs : x~a, xs~Vec a m, n == m + 1

fn area s -> n : s~Shape, n~Nat
    match s
        Circle r -> 3 * r * r
        Rect w h -> w * h

fn manhattan p -> d : p~Point, d~Int
    p.x + p.y

fn first xs -> r : xs~List a, r~Option a
    match xs
        []     -> None
        x :: _ -> Some x

fn vlength v -> n : v~Vec a k, n~Nat
    match v
        VNil       -> 0
        VCons _ xs -> 1 + vlength xs

fn swap p -> q : p~(a, b), q~(b, a)
    let (x, y) = p
    (y, x)

fn classify n -> s : n~Nat, s~String
    match n
        0 -> "zero"
        1 -> "one"
        _ if n < 10 -> "small"
        _ -> "large"

fn ops xs -> r : xs~List Nat, r~List Nat
    let inc = (+ 1)
    let twice = \f x -> f (f x)
    let composed = inc . inc
    map composed (reverse $ map (twice inc) xs)

fn sum_pairs ps -> n : ps~List (Nat, Nat), n~Nat
    match ps
        []             -> 0
        (a, b) :: rest -> a + b + sum_pairs rest

fn zip_len xs ys -> n : xs~List a, ys~List b, n~Nat
    match (xs, ys)
        (_ :: xr, _ :: yr) -> 1 + zip_len xr yr
        _                  -> 0

fn parse_digit b -> r : b~U8, r~Result Nat String
    if '0' <= b and b <= '9' then Ok (b - '0') else Err "not a digit"

fn parse_two a b -> r : a~U8, b~U8, r~Result Nat String
    let x = try parse_digit a
    let y = try parse_digit b
    Ok (x * 10 + y)

fn bounded n -> b : n~Nat, b~Bounded 10
    Bounded (if n > 10 then 10 else n)

fn parallel_sum xs ys -> n : xs~List Nat, ys~List Nat, n~Nat
    let (a, b) = par (length xs, length ys)
    a + b

let ORIGIN = Point 0 0

check area (Rect 2 3) == 6
check length [1, 2, 3] == 3
check manhattan ORIGIN == 0
