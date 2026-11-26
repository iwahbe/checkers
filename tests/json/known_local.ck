# A local whose value is known at compile time stands for that value in
# arithmetic: `c + 1` has the range `8 + 1` would have, which `d`'s hover
# shows. `next` is another module's function, whose value is computed by
# running it.
module known_local

import lib.known (next, SEVEN)

export fn by_call -> r : r~Int
    let c = next 7
    let d = c + 1
    d

export fn by_name -> r : r~Int
    let c = SEVEN
    let d = c + 1
    d

export fn by_alias -> r : r~Int
    let c = next 7
    let e = c
    let d = e + 1
    d

export fn by_tuple k -> r : k~Int, r~Int
    let (c, _) = (next 7, k)
    let d = c + 1
    d

export fn by_match k -> r : k~Int, r~Int
    match (next 7, k)
        (c, _) ->
            let d = c + 1
            d

export fn by_have -> r : r~Int
    let c = next 7
    have c~Int
    let d = c + 1
    d

export fn by_lambda -> r : r~Int
    let f = \_ -> next 7
    let c = f 0
    let d = c + 1
    d

# A function of this module: known once it is proved, which it is on
# demand.
fn twice x -> r : x~Int, r~Int
    x * 2

export fn by_own -> r : r~Int
    let c = twice 4
    let d = c + 1
    d

# A part of a value a call builds: not known, as the call isn't unfolded
# to find it.
fn pair k -> r : k~Int, r~(Int, Int)
    (k, next 7)

export fn by_unfold k -> r : k~Int, r~Int
    let p = pair k
    let (_, c) = p
    let d = c + 1
    d

# Computed from a parameter: not known.
export fn by_param k -> r : k~Int, r~Int
    let c = k
    let d = c + 1
    d
