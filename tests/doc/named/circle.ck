# circle.ck — circles.
module circle

# The width of a circle of radius `r`.
export fn diameter r -> d : r~Nat, d~Nat
    2 * r
