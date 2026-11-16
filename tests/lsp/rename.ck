module rename

record Point
    x~Nat
    y~Nat

fn shift p -> r : p~Point, r~Point
    Point (p.x + 1) p.y

export fn sum p -> n : p~Point, n~Nat
    let q = shift p
    q.x + q.y
