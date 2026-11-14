module statement

import std.sort

record Point
    x~Int
    y~Int

fn norm p -> n : p~Point, n~Int
    p.x * p.x + p.y * p.y

# At the start of a statement in a body.
fn after p -> n : p~Point, n~Int
    let q = p
    ‸

# Keywords: `let`, `have`, `when`, `if`, `match`, `try`, `par`.
# Not: `fn`, `lemma`, `ensures`, `proof`, `auto` (not in a `proof`).
# Names, in this order:
#   locals:    q : Point, p : Point, n : Int (the result, in conditions only: not here)
#   module:    norm, after, Point
#   imported:  sort (the module), and the prelude's names
# `q` and `p` first among the locals: nearest binding first.
