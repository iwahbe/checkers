# A tuple pattern can't take `()` apart: it has no parts.
module tuple_pattern_on_unit

fn by_match u -> r : u~(), r~Int
    match u
        (_, _) -> 0

fn by_let u -> r : u~(), r~Int
    let (a, b, c) = u
    0

# `()` as the rest of a tuple is one part, not none.
fn unit_last p -> r : p~(Int, ()), r~Int
    let (a, b, c) = p
    a
