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

# A container of the module's own.
export enum Bin a
    Tip
    Fork l v r : l~Bin a, v~a, r~Bin a

# Whether `x` is in `t`: true only where `x` equals a part of `t`.
export transparent fn holds t x -> r : t~Bin a, x~a, r~Bool
    match t
        Tip        -> False
        Fork l v r -> v == x or holds l x or holds r x

# Its body is sealed; its signature promises with the module's own `holds`.
export fn each_in t p -> r : t~Bin a, p~(x~a -> Bool, holds t x), r~Bool
    match t
        Tip        -> True
        Fork l v r -> p v and each_in l p and each_in r p

# Not a membership: true of anything when `t` isn't empty.
export transparent fn filled t x -> r : t~Bin a, x~a, r~Bool
    match t
        Tip        -> False
        Fork _ _ _ -> True

export fn each_filled t p -> r : t~Bin a, p~(x~a -> Bool, filled t x), r~Bool
    match t
        Tip        -> True
        Fork l v r -> p v and each_filled l p and each_filled r p

# A membership whose body is sealed, so importers can't see that it is one.
export fn sealed_holds t x -> r : t~Bin a, x~a, r~Bool
    match t
        Tip        -> False
        Fork l v r -> v == x or sealed_holds l x or sealed_holds r x

export fn each_sealed t p -> r : t~Bin a, p~(x~a -> Bool, sealed_holds t x), r~Bool
    match t
        Tip        -> True
        Fork l v r -> p v and each_sealed l p and each_sealed r p
