# An arm the arms above already cover is still checked, then warned
# never to match: its pattern against the type of the value matched, its
# body against the type of the result. So is an alternative of a `|`
# pattern that the arms above cover.
module unreachable_arm_checked

fn after_wild x -> r : x~Int, r~Int
    match x
        _      -> 0
        (a, b) -> 1

fn after_var x -> r : x~Int, r~Int
    match x
        y      -> y
        (a, b) -> 1

fn after_unit u -> r : u~Unit, r~Int
    match u
        ()     -> 0
        (a, b) -> 1

fn first_on_unit u -> r : u~Unit, r~Int
    match u
        (a, b) -> 1

fn body x -> r : x~Int, r~Int
    match x
        _ -> 0
        y -> "y"

fn nested o -> r : o~Option Int, r~Int
    match o
        Some _      -> 0
        Some (a, b) -> 1
        None        -> 2

fn alternative o -> r : o~Option Int, r~Int
    match o
        Some _             -> 0
        None | Some (a, b) -> 1
