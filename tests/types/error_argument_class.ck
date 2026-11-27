module error_argument_class

import std.parse (Parsable)

# What an argument that failed to check would decide isn't known, because
# of its error: only that error is reported, not the class clauses, nor
# what else depends on the type it would give.

fn walk xs -> r : Seq s, xs~s, r~Int
    0

fn pick x -> r : x~a, r~a
    x

fn by_name u -> r : u~Unit, r~Int
    walk nothing

fn by_module u -> r : u~Unit, r~Int
    walk parse

# The error inside the type the argument gives.
fn in_tuple u -> r : u~Unit, r~Int
    walk (missing_a, 1)

# The unknown passed on: through a `let`, a function's result, an operator.
fn by_let u -> r : u~Unit, r~Int
    let y = pick missing_b
    walk y

fn by_result u -> r : u~Unit, r~Int
    let f = \x -> missing_c
    walk (f 1)

fn by_operator u -> r : u~Unit, r~Int
    walk (missing_d + 1)

fn by_field u -> r : u~Unit, r~Int
    let y = pick missing_e
    y.size
