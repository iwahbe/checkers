# shapes.ck — shapes and their areas. This line and the next are the module's
# description; its first sentence is shown in the package's index.
module pkg.shapes

import pkg.sub.broken (Kind)
import pkg.sub.broken as b

# A point. The fields are shown, each with its description.
export record Point
    # Across.
    x~Int
    y~Int

# A shape:
#
# - a circle, by its radius;
# - a rectangle, by its sides.
export enum Shape
    # A circle.
    Circle r : r~Nat
    Rect w h : w~Nat, h~Nat

# Its constructors are hidden, so they aren't shown.
export abstract enum Handle

# An even number.
export type Even = n~Nat, n % 2 == 0

# Twice the area, in whole units (`Circle` uses 3 for pi). A long
# signature keeps its lines:
export fn double_area s -> a : s~Shape,
                               a~Nat
    match s
        Circle r -> 6 * r * r
        Rect w h -> 2 * w * h

# Counts down; `decreasing` isn't part of the signature.
export fn down n -> r : n~Nat, r~Nat
    decreasing n
    if n == 0 then 0 else down (n - 1)

# Areas aren't negative.
export lemma nonneg s : s~Shape
    ensures double_area s >= 0
    proof
        auto

# Links: `Kind` through the import's names, `b.Square` through its name;
# `Round` isn't one (the import doesn't bring it in).
export fn kind s -> k : s~Shape, k~Kind, k == Round or k == b.Square
    match s
        Circle _ -> Round
        Rect _ _ -> Square

export fn same k -> r : k~b.Kind, r~b.Kind
    k

# `Circle` is a constructor here; `Option` and `Some` are the prelude's, not
# this package's.
export fn maybe s -> m : s~Shape, m~Option Shape, m == Some s or s == Circle 0
    Some s

export let UNIT = 1

# A table too long to show.
export let TABLE = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

export fn undocumented x -> y : x~Int, y~Int
    x

# Not exported: not documented.
fn hidden x -> y : x~Int, y~Int
    x

check down 3 == 0
