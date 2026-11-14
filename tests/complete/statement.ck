module statement

# Names and keywords in a function's body (D142).
import std.char

# A point in the plane.
record Point
    x~Int
    y~Int

# Its distance from the origin, squared.
fn norm p -> n : p~Point, n~Int
    p.x * p.x + p.y * p.y

# A statement: locals first (nearest first), keywords, this module's
# names, then the prelude's and the imported module.
fn after p -> n : p~Point, n~Int
    let q = p
    ‸

# The first statement of a body: `decreasing` too. A name being typed
# is replaced.
fn first p -> n : p~Point, n~Int
    no‸

# An argument whose type is known: those of that type first.
fn arg p -> n : p~Point, n~Int
    norm ‸

# A record's fields, a module's exports.
fn fields p -> n : p~Point, n~Int
    p.‸

fn exports c -> n : c~Char, n~Nat
    char.‸

# After a multi-line `if`'s branch: `else`.
fn branch p -> n : p~Point, n~Int
    if p.x > 0
        1
    ‸

# A statement that doesn't parse yet: what is in scope is still known.
fn unfinished p -> n : p~Point, n~Int
    let q = p
    norm (‸q.
