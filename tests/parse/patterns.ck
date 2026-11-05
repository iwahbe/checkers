module patterns

fn shapes v
    match v
        Null | Bool _          -> 0
        Arr []                 -> 1
        Arr [x]                -> 2
        Arr (x :: y :: rest)   -> 3
        Pair (a, (b, _))       -> 4
        Num 0                  -> 5
        Num -1                 -> 6
        Some b if b < 0x20     -> 7
        Some '"'               -> 8
        Str "x"                -> 9
        ()                     -> 10
        _                      -> \(k, x) y -> k
