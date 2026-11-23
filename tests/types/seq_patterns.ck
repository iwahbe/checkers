module seq_patterns

# `[]`, `x :: rest` and `[p1, …, pn]` take apart any type with a `Seq`
# instance: a clause `Seq s`, arrays, bytes and strings. No `decreasing`:
# the guessed measure is the sequence's size.

import std.array

fn count xs -> n : Seq s, xs~s, n~Nat
    match xs
        []        -> 0
        _ :: rest -> 1 + count rest

check count [1, 2, 3] == 3
check count (array.from_list [1, 2, 3]) == 3
check count b"abcd" == 4
check count "h€llo" == 5

# Nested patterns take the rest apart again.
fn first_two xs -> r : Seq s, xs~s, r~Option (Seq.Elem s, Seq.Elem s)
    match xs
        x :: y :: _ -> Some (x, y)
        _           -> None

check first_two "h€llo" == Some (c'h', c'€')
check first_two b"a" == None

# A literal pattern is an exact length.
fn exactly_two xs -> r : Seq s, xs~s, r~Bool
    match xs
        [_, _] -> True
        _      -> False

check exactly_two "ab" and not (exactly_two "abc") and not (exactly_two "a")

# At a known instance the element's type is the instance's.
fn sum b -> n : b~Bytes, n~Nat
    match b
        []        -> 0
        x :: rest -> x + sum rest

check sum b"\x01\x02\x03" == 6

fn first_char s -> c : s~String, c~Option Char
    match s
        []     -> None
        c :: _ -> Some c

check first_char "€x" == Some c'€'

# A size fact in a `::` arm is a fact for the prover too.
fn shorter xs -> r : Seq s, xs~s, r~Bool, r
    match xs
        []        -> True
        _ :: rest -> Seq.size rest < Seq.size xs

# On a list, a `match` is unchanged: its constructors and these patterns
# mix as before.
fn len_list xs -> n : xs~List a, n~Nat
    match xs
        Nil       -> 0
        _ :: rest -> 1 + len_list rest

# At a known instance the prover sees its `uncons`: a non-empty array has
# no `[]` case, and `std.array` says what the rest is.
fn rest_slice xs -> r : xs~Array Int, len xs > 0, r~Bool, r
    match xs
        _ :: rest ->
            have array.uncons_slice xs
            rest == array.slice xs 1 (len xs)
