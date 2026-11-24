module match_uncons

# A `match` on `Seq.uncons xs` whose arms sequence patterns can write is
# W011: `None` is `[]` and `Some (x, rest)` is `x :: rest`.

fn by_uncons xs -> n : Seq s, xs~s, n~Nat
    match Seq.uncons xs
        Some (_, rest) -> 1 + by_uncons rest
        None           -> 0

# At a known instance, with a wildcard, an or-pattern and a nested pattern.
fn wild xs -> b : xs~List Int, b~Bool
    match Seq.uncons xs
        Some _ -> True
        _      -> False

fn either xs -> b : xs~List Int, b~Bool
    match Seq.uncons xs
        None | Some (0, _) -> True
        Some _             -> False

fn nested xs -> b : xs~List (List Int), b~Bool
    match Seq.uncons xs
        Some (x :: _, _) -> x == 0
        _                -> False

# The sequence is not a variable.
fn of_call xs -> b : xs~List Int, b~Bool
    match Seq.uncons (0 :: xs)
        Some _ -> True
        None   -> False

# Not warned: an arm binds the `Option` or the pair.
fn whole xs -> r : xs~List Int, r~Option (Int, List Int)
    match Seq.uncons xs
        Some p -> Some p
        r      -> r

# Not warned: a `match` on the sequence.
fn sugared xs -> n : Seq s, xs~s, n~Nat
    match xs
        _ :: rest -> 1 + sugared rest
        []        -> 0
