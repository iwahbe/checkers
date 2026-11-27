module let_refutable

import std.list

# A `let`'s pattern, like a `match`, covers the values that can occur
# (#633): cases the facts in scope rule out needn't be handled. One that
# can occur is E0240, about the pattern.

fn first l -> x : l~List a, len l > 0, x~a
    let x :: _ = l
    x

fn second p -> y : p~Option (Int, Int), p != None, y~Int
    let Some (_, y) = p
    y

fn sum_firsts ls -> n : ls~List (List Int), n~Int
    let firsts = list.map (\(x :: _) -> x) ls
    0

fn careless l -> x : l~List Int, x~Int
    let x :: _ = l
    x

check first [1, 2] == 1
check second (Some (1, 2)) == 2
