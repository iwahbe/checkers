module lambda_later_call

# A lambda's parameter takes the type of a later argument that is a call whose
# result type depends on the call's own arguments, as it does when the call is
# bound with `let` first: the order of the arguments doesn't decide whether a
# program checks.
fn find_lt b i -> r : b~Bytes, i~Nat, r~Option (j~Nat, i <= j, j < len b)
    if i < len b then Some i else None

fn omap g o -> r : g~(a -> c), o~Option a, r~Option c
    match o
        None   -> None
        Some x -> Some (g x)

fn by_call b i -> r : b~Bytes, i~Nat, r~Option (k~Nat, i < k, k <= len b)
    omap (\j -> j + 1) (find_lt b i)

fn by_let b i -> r : b~Bytes, i~Nat, r~Option (k~Nat, i < k, k <= len b)
    let o = find_lt b i
    omap (\j -> j + 1) o

fn by_fmap b i -> r : b~Bytes, i~Nat, r~Option (k~Nat, i < k, k <= len b)
    fmap (\j -> j + 1) (find_lt b i)
