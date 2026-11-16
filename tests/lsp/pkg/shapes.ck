module shapes

export record Point
    x~Nat
    y~Nat

# The area of a [Point], [`Point.x`] times its `y`:
#
# ```
# import shapes (Point, area)
#
# check area (Point 2 3) == 6
# ```
export fn area p -> n : p~Point, n~Nat
    p.x * p.y

export let ORIGIN = Point 0 0
