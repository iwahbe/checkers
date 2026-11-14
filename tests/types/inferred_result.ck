# A result whose type isn't written is the same type for every call: two
# recursive calls with different arguments add up.
module inferred_result

partial fn fib x -> n : x~Nat
    if x == 0 or x == 1 then 1 else fib (x - 1) + fib (x - 2)

# A type parameter it can still be.
fn first x y -> r : x~a, y~a
    x

check fib 6 == 13
check first 1 2 == 1
