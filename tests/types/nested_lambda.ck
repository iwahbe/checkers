module nested_lambda

import std.list

fn shift xs i -> r : xs~List Int, i~Int, r~Int
    match xs
        []        -> i
        x :: rest -> x + shift rest i

# The same partial application inside a lambda and outside it.
lemma map_step ks ys y rest : ks~List Int, ys~List Int, y~Int, rest~List Int, ys == y :: rest
    ensures list.map (shift (list.map (shift ks) ks)) ys == shift (list.map (shift ks) ks) y :: list.map (shift (list.map (shift ks) ks)) rest
    proof
        auto
