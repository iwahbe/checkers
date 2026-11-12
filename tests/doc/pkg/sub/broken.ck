# A module with a type error still has documentation: <b>escaped</b> & all.
module pkg.sub.broken

# Returns a `String` where an `Int` is expected.
export fn wrong x -> y : x~Int, y~Int
    "no"
