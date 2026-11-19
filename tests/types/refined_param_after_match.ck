# A function parameter whose precondition mentions an earlier parameter
# keeps it after a `match` on that parameter, generic or not.
module refined_param_after_match

fn mem xs y -> r : xs~List Int, y~Int, r~Bool
    match xs
        []        -> False
        x :: rest -> x == y or mem rest y

# In the `x :: rest` arm, `p`'s precondition is `mem (x :: rest) y`.
fn each xs p -> r : xs~List Int, p~(y~Int -> Bool, mem xs y), r~Bool
    match xs
        []        -> True
        x :: rest -> p x and each rest p

fn mem_of xs y -> r : xs~List a, y~a, r~Bool
    match xs
        []        -> False
        x :: rest -> x == y or mem_of rest y

# The same over any element type.
fn each_of xs p -> r : xs~List a, p~(y~a -> Bool, mem_of xs y), r~Bool
    match xs
        []        -> True
        x :: rest -> p x and each_of rest p
