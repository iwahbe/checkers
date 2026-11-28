module lambda_unfold_subst

import std.list

enum Tree
    Leaf i  : i~Int
    Node ts : ts~List Tree

fn shift xs i -> r : xs~List Int, i~Int, r~Int
    match xs
        []        -> i
        x :: rest -> x + shift rest i

fn walk xs t -> r : xs~List Int, t~Tree, r~Tree
    match t
        Leaf i  -> Leaf (shift xs i)
        Node ts -> Node (list.map (walk xs) ts)

# One unfolding of `walk`, whose body maps a partial application, at an
# argument that is itself a partial application mapped.
lemma by_map ks ts : ks~List Int, ts~List Tree
    ensures walk (list.map (shift ks) ks) (Node ts) == Node (list.map (walk (list.map (shift ks) ks)) ts)
    proof
        auto
