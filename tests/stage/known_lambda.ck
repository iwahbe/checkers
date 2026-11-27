module known_lambda

# A lambda's closure known at compile time is shown as its code with the
# values it captured put in (§8.9): `adder 2` is `\x -> x + 4`.

fn adder n -> f : n~Int, f~(Int -> Int)
    let m = n * n
    \x -> x + m

fn apply_all f xs -> ys : f~comptime (Int -> Int), xs~List Int, ys~List Int
    match xs
        []        -> []
        x :: rest -> f x :: apply_all f rest

fn by_two xs -> ys : xs~List Int, ys~List Int
    apply_all (adder 2) xs
