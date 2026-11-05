# list.ck — functions on immutable lists.
module list

export fn length xs -> n : xs~List a, n~Nat
    match xs
        [] -> 0
        _ :: rest -> 1 + length rest

export fn map f xs -> ys : f~(a -> b), xs~List a, ys~List b
    match xs
        [] -> []
        x :: rest -> f x :: map f rest

export fn all p xs -> r : p~(a -> Bool), xs~List a, r~Bool
    match xs
        [] -> True
        x :: rest -> p x and all p rest

export fn reverse xs -> ys : xs~List a, ys~List a
    reverse_onto xs []

fn reverse_onto xs acc -> ys : xs~List a, acc~List a, ys~List a
    match xs
        [] -> acc
        x :: rest -> reverse_onto rest (x :: acc)

export fn join sep parts -> s : sep~String, parts~List String, s~String
    match parts
        [] -> ""
        [p] -> p
        p :: rest -> p ++ sep ++ join sep rest

export fn keys pairs -> ks : pairs~List (k, v), ks~List k
    match pairs
        [] -> []
        (key, _) :: rest -> key :: keys rest

export fn contains xs x -> r : xs~List a, x~a, r~Bool
    match xs
        [] -> False
        y :: rest -> y == x or contains rest x

export fn unique xs -> r : xs~List a, r~Bool
    match xs
        [] -> True
        x :: rest -> not (contains rest x) and unique rest

export fn count x xs -> n : x~a, xs~List a, n~Nat
    match xs
        [] -> 0
        y :: rest -> (if y == x then 1 else 0) + count x rest

export fn max_of xs -> m : xs~List Nat, m~Nat
    match xs
        [] -> 0
        x :: rest ->
            let m = max_of rest
            if x > m then x else m

export fn take n xs -> ys : n~Nat, xs~List a, ys~List a
    match xs
        [] -> []
        x :: rest -> if n == 0 then [] else x :: take (n - 1) rest

export fn drop n xs -> ys : n~Nat, xs~List a, ys~List a
    match xs
        [] -> []
        _ :: rest -> if n == 0 then xs else drop (n - 1) rest

export fn sorted xs -> r : xs~List Int, r~Bool
    decreasing length xs
    match xs
        x :: y :: rest -> x <= y and sorted (y :: rest)
        _ -> True

export fn perm xs ys -> r : xs~List Int, ys~List Int, r~Bool
    length xs == length ys and all (\x -> count x xs == count x ys) xs
