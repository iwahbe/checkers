module complete

record Point
    x~Int
    y~Int

# Its distance from the origin, squared.
fn norm p -> n : p~Point, n~Int
    p.x * p.x + p.y * p.y

fn twice p -> n : p~Point, n~Int
    norm p + norm p
