# The pattern `()` matches a value of type `()`, and no other.
module unit_pattern_type

fn whole x -> r : x~Int, r~Int
    match x
        () -> 0

fn part p -> r : p~(Int, Int), r~Int
    let (a, ()) = p
    a

fn unit u -> r : u~(), r~Int
    match u
        () -> 0

fn some o -> r : o~Option (), r~Int
    match o
        Some () -> 1
        None    -> 0

check some (Some ()) == 1
check unit () == 0
