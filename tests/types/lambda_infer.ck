module lambda_infer

# A lambda whose type is inferred (not checked against a function type)
# may take its parameters apart with a pattern, and its result type may be
# settled where it is applied.

fn sum p -> r : p~(Int, Int), r~Int
    (\(a, b) -> a + b) p

fn first p -> r : p~(Int, Int), r~Int
    let pick = \(a, _) -> a
    pick p

fn one x -> r : x~Int, r~Int
    let g = \q -> 1
    g x

check (\(a, b) -> a + b) (1, 2) == 3
check sum (2, 3) == 5
check first (4, 5) == 4
check one 9 == 1

fn later x -> r : x~Int, r~Int
    let g = \z ->
        let w = z + 1
        w * 2
    let x = x + 1
    g x

check later 1 == 6
