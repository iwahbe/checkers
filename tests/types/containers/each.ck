# Functions that call their function argument only with elements of a list,
# for `termination_across_modules`.
module containers.each

import std.list

# Its body is sealed and its signature promises nothing.
export fn hidden xs p -> r : xs~List a, p~(a -> Bool), r~Bool
    match xs
        []        -> True
        x :: rest -> p x and hidden rest p

# Its body is visible to importers.
export transparent fn shown xs p -> r : xs~List a, p~(a -> Bool), r~Bool
    match xs
        []        -> True
        x :: rest -> p x and shown rest p

# Its body is sealed and its signature makes the promise.
export fn promised xs p -> r : xs~List a, p~(x~a -> Bool, list.contains xs x), r~Bool
    match xs
        []        -> True
        x :: rest -> p x and promised rest p
