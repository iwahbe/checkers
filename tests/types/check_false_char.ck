module check_false_char

# A false `check` shows characters as characters, not as their codes.
check Some (c'😀', 4) == Some (c'a', 4)
check [c'é', c'\n'] == []
check (c'\'', c'\\', c'\t', c'\u{1}', 7) == (c'a', c'b', c'c', c'd', 7)

fn first cs -> r : cs~List Char, r~Result Char String
    match cs
        c :: _ -> Ok c
        []     -> Err "empty"

check first [c'é'] == first []
