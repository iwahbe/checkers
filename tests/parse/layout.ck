module layout

# A trailing comma, a leading operator, and a leading `:` all continue a line.
fn long_header a b c -> r : a~Nat, b~Nat,
                            c~Nat, r~Nat
    a + b
      + c

lemma split_header x
    : x~Nat
    ensures x == x

# Inside brackets newlines are ignored.
fn listed -> xs : xs~List Nat
    [ 1,
      2,
      3 ]

# A trailing `->` opens a block; multi-line `let` and `if`/`else if`/`else`.
fn classify n : n~Int
    let sign =
        let zero = 0
        if n < zero then -1 else 1
    match n
        0 ->
            "zero"
        _ ->
            if sign < 0
                "negative"
            else if n < 10
                "small"
            else
                "large"
