module signature_match_body

# A `match` in a signature's continuation lines, then the body, one level in
# from `fn`.
export fn pick o -> r : o~Option Int, r~Int,
                        match o
                            None   -> r == 0
                            Some x -> r == x
    match o
        None   -> 0
        Some x -> x
