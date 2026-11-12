module docs

import std.list

# A point on the grid.
#
# Both coordinates count from the top left.
record Point
    # Across.
    x~Nat
    y~Nat

# The point `n` steps to the right of `p`.
fn right p n -> q : p~Point, n~Nat, q~Point, q.x == p.x + n
    Point (p.x + n) p.y

fn undocumented p -> q : p~Point, q~Point
    right p 1

let LEFT = list.reverse [right (Point 0 0) 2]
