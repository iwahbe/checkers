module app

import shapes (Point, area)

export fn twice p -> n : p~Point, n~Nat
    let size = area p
    size + size
