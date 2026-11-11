module demo

# A record, a function with a postcondition, and a type error.
record Point
    x~Nat
    y~Nat

let ORIGIN = Point 0 0

fn sum p -> r : p~Point, r~Nat, r > 100
    p.x + p.y

fn bad -> r : r~String
    1
