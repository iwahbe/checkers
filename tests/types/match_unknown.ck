# A `match` whose type is inferred (a `let` without a type), where an arm
# gives it an unknown made inside a nested pattern: `None`'s type parameter
# can't depend on the arm's names, so it is solved outside the `match`
# (pruning). It was E0201 "expected `_`, found `Option ?a`".
module match_unknown

fn first r -> o : r~Result (List Int) String, o~Option Int
    let x = match r
        Ok (l :: _) -> Some l
        _           -> None
    x

fn nested r -> o : r~Result (List (List Int)) String, o~Option Int
    let x = match r
        Ok (l :: _) ->
            match l
                t :: _ -> Some t
                []     -> None
        _           -> None
    x

check first (Ok [3, 4]) == Some 3
check first (Ok []) == None
check nested (Ok [[], [5]]) == None
check nested (Ok [[5]]) == Some 5
check nested (Err "no") == None
