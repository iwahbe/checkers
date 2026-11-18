module tuple_result_recursive

# A refined part of a function's tuple result holds at every call, the
# function recursive or not, once the result is taken apart.

fn walk n i -> r : n~Nat, i~Nat, i <= n, r~(Nat, (j~Nat, i <= j, j <= n))
    decreasing n - i
    if i < n then walk n (i + 1) else (0, i)

fn by_let n i -> r : n~Nat, i~Nat, r~Option (Nat, (j~Nat, i < j, j <= n))
    if i < n
        let (a, j) = walk n (i + 1)
        Some (a, j)
    else
        None

fn by_match n i -> r : n~Nat, i~Nat, r~Option (Nat, (j~Nat, i < j, j <= n))
    if i < n
        match walk n (i + 1)
            (a, j) -> Some (a, j)
    else
        None

fn walk_nested n i -> r : n~Nat, i~Nat, i <= n, r~(Nat, (Nat, (j~Nat, i <= j)))
    decreasing n - i
    if i < n then walk_nested n (i + 1) else (0, (1, i))

fn by_nested_let n i -> r : n~Nat, i~Nat, i <= n, r~(j~Nat, i <= j)
    let (_, (_, j)) = walk_nested n i
    j
