module index

# Names in the index (§15.5): declarations, parameters, `let`, lambdas,
# patterns, constructors, record fields, qualified names.
import std.list

record Point
    x~Nat
    y~Nat

enum Shape
    Dot p    : p~Point
    Line a b : a~Point, b~Point

fn width s -> w : s~Shape, w~Nat
    match s
        Dot _    -> 0
        Line a b ->
            let dx = if a.x < b.x then b.x - a.x else a.x - b.x
            dx

fn widths shapes -> ws : shapes~List Shape, ws~List Nat
    list.map (\sh -> width sh) shapes
