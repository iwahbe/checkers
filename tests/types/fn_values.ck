module fn_values

# Function values in proofs (M22, D139): a function the prover doesn't know
# (a parameter, a lambda using local variables, a function in a record) is a
# value it can pass, apply and reason about.

import std.list (map, length)

# A lemma about `map` for any function, proved by induction.
lemma map_keeps_length f xs : f~(a -> b), xs~List a
    ensures length (map f xs) == length xs
    proof
        match xs
            []        -> auto
            _ :: rest -> have map_keeps_length f rest

# Using it at a function parameter.
fn same_length f xs -> n : f~(Int -> Int), xs~List Int, n~Nat, n == length xs
    have map_keeps_length f xs
    length (map f xs)

# A lambda that uses a local variable.
fn shifted k -> r : k~Int, r~List Int, r == [1 + k, 2 + k]
    map (\x -> x + k) [1, 2]

fn first_or xs d -> r : xs~List Int, d~Int, r~Int
    match xs
        []     -> d
        x :: _ -> x

fn first_shifted xs k -> r : xs~List Int, k~Int, r~Bool, r
    first_or (map (\x -> x + k) xs) k == first_or xs 0 + k

# A partial application of a parameter, passed on.
fn adds f k xs -> r : f~(Int -> Int -> Int), k~Int, xs~List Int, r~List Int, length r == length xs
    have map_keeps_length (f k) xs
    map (f k) xs

# The postcondition of an unknown function, through `map` (D84).
fn bigger f xs -> r : f~(x~Int -> y~Int, y > x), xs~List Int, r~Bool, r
    first_or (map f [0]) 0 > 0

# A function in a record.
record Step
    run~(Int -> Int)

fn step_twice s x -> r : s~Step, x~Int, r~Int, r == s.run (s.run x)
    s.run (s.run x)

fn make k -> s : k~Int, s~Step, s.run 0 == k
    Step (\x -> x + k)

# Wrong: nothing is known about `f`.
fn guess f xs -> r : f~(Int -> Int), xs~List Int, r~Bool, r
    first_or (map f [1]) 0 == 1

check shifted 3 == [4, 5]
check step_twice (make 2) 1 == 5
