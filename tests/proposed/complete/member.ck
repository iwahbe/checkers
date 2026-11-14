module member

import std.sort
import std.char

record Point
    x~Int
    y~Int

fn after p -> n : p~Point, n~Int
    let q = p
    q.‸

# After `x.` with `x` a record: its fields, with their types.
#   x : Int    (field of `Point`)
#   y : Int    (field of `Point`)
# No keywords. Typing `q.y` narrows to `y`.
#
# The same place after a module, `char.‸`, gives its exports:
#   code, from_scalar, from_ascii, from_surrogates   (with signatures)
# and after a class, `Ord.‸`: le, trans, total, antisym.
#
# Today `q.` at the end of a line continues onto the next line, so the
# next declaration is lost with it (D142 e 2).
