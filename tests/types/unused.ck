# Unused code (D144): `main` is the root; `check`s, lemmas and instances
# count as uses; anything else no root reaches is reported.
module unused

import std.system (System, ExitCode)
import unused_parts (used_part)

# Unused, though they call each other.
partial fn ping n -> r : n~Nat, r~Nat
    match n
        0 -> 0
        _ -> pong (n - 1)

partial fn pong n -> r : n~Nat, r~Nat
    match n
        0 -> 0
        _ -> ping (n - 1)

# Used only by a `check`: used.
fn tested n -> r : n~Int, r~Int
    n + 1

check tested 1 == 2

# Used only in a postcondition: used.
fn small n : n~Int
    n < 10

fn ten -> r : r~Int, small r
    9

# Never built, never read.
enum Shape
    Square s       : s~Nat
    Circle r       : r~Nat
    Triangle a b c : a~Nat, b~Nat, c~Nat

record Size
    width~Nat
    height~Nat

fn area s -> n : s~Shape, n~Nat
    match s
        Square x -> x * x
        _        -> 0

fn width z -> n : z~Size, n~Nat
    z.width

record Unused
    x~Int

# A `match` arm the ones above already cover.
fn sign n -> r : n~Int, r~Int
    match n
        0 -> 0
        _ -> 1
        1 -> 2

# Branches that can't run.
fn first xs -> r : xs~List Int, xs != [], r~Int
    match xs
        []     -> 0
        x :: _ -> x

fn negative n -> r : n~Nat, r~Bool
    if n < 0 then True else False

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let n = area (Square 2) + width (Size 1 2)
    if first [sign ten, used_part n] > 0 and not (negative n) then Success else Failure 1
