module shapes

export record Point
    x~Nat
    y~Nat

export fn area p -> n : p~Point, n~Nat
    p.x * p.y

export let ORIGIN = Point 0 0
