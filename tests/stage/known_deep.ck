module known_deep

# A value a million constructors deep, computed at compile time, is a
# compile-time argument: staging takes it apart one level at a time, and
# runs code on what it gives as static data, so a `match` on it and code
# using it take the same stack at any depth.

enum Chain
    End
    Link c n : c~Chain, n~Nat

fn grow c n -> r : c~Chain, n~Nat, r~Chain
    decreasing n
    if n == 0 then c else grow (Link c 1) (n - 1)

fn top c -> n : c~comptime Chain, n~Nat
    match c
        End      -> 0
        Link _ k -> k

fn by_match x -> n : x~Nat, n~Nat
    top (grow End 1000000) + x

fn rest c -> r : c~comptime Chain, r~Chain
    match c
        End      -> End
        Link r _ -> r

fn length c acc -> n : c~Chain, acc~Nat, n~Nat
    match c
        End      -> acc
        Link r _ -> length r (acc + 1)

fn run_on x -> n : x~Nat, n~Nat
    length (rest (grow End 1000000)) 0 + x

check by_match 1 == 2 and run_on 1 == 1000000
