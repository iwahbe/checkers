module tuple_result_recursive

# A refined part of a function's tuple result holds at every call, the
# function recursive or not, once the result is taken apart.

fn more src i -> r : src~Bytes, i~Nat, i <= len src, r~(Nat, (j~Nat, i <= j, j <= len src))
    decreasing len src - i
    if i < len src then more src (i + 1) else (0, i)

fn digits src i -> r : src~Bytes, i~Nat, r~Option (Nat, (j~Nat, i < j, j <= len src))
    if i < len src
        let (n, j) = more src (i + 1)
        Some (n, j)
    else
        None

fn by_match src i -> r : src~Bytes, i~Nat, r~Option (Nat, (j~Nat, i < j, j <= len src))
    if i < len src
        match more src (i + 1)
            (n, j) -> Some (n, j)
    else
        None

fn nested src i -> r : src~Bytes, i~Nat, i <= len src, r~(Nat, (Nat, (j~Nat, i <= j)))
    decreasing len src - i
    if i < len src then nested src (i + 1) else (0, (1, i))

fn last src i -> r : src~Bytes, i~Nat, i <= len src, r~(j~Nat, i <= j)
    let (_, (_, j)) = nested src i
    j
