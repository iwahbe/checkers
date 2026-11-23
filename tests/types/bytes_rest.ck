module bytes_rest

# What `x :: rest` leaves of bytes is the bytes after the first.

fn rest_of xs -> r : xs~Bytes, r~Option Bytes
    match xs
        _ :: rest -> Some rest
        []        -> None

lemma rest_of_cons post : post~Bytes
    ensures rest_of (b"a" ++ post) == Some post
    proof
        auto

# Taking `k` bytes off, one at a time.
fn skip xs k -> r : xs~Bytes, k~Nat, r~Bytes
    match xs
        _ :: rest -> if k == 0 then xs else skip rest (k - 1)
        []        -> xs

lemma skip_append a b : a~Bytes, b~Bytes
    ensures skip (a ++ b) (len a) == b
    proof
        match a
            []        -> auto
            _ :: rest -> have skip_append rest b
