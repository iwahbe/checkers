module debug_elsewhere

# Only a type's own module may replace its derived `Debug`: elsewhere in
# its package the instance overlaps the derived one (E0283), in another
# package it breaks the orphan rule (E0282). It takes no context (E0281).

import std.string (Debug)
import shapes.point (Point)

instance Debug Point
    fn debug p
        "point"

instance Debug Int
    fn debug n
        "int"

record Box a
    item~a

instance Debug (Box a) : Debug a
    fn debug b
        "box"
