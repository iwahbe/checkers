module functor_map

# Benchmark (§14): a function generic over a class over type constructors,
# at a tree type and at `List`, and the same function written for each.
# `functor_map generic` or `functor_map mono`; both print the same.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (format)

# A container whose elements a function can be applied to.
class Mappable f
    fn mapping g xs -> ys : g~(a -> b), xs~f a, ys~f b

enum Tree a
    Leaf
    Node l x r : l~Tree a, x~a, r~Tree a

instance Mappable Tree
    fn mapping g t
        match t
            Leaf       -> Leaf
            Node l x r -> Node (mapping g l) (g x) (mapping g r)

instance Mappable List
    fn mapping g xs
        match xs
            []        -> []
            x :: rest -> g x :: mapping g rest

fn tree n -> t : n~Nat, t~Tree Int
    decreasing n
    if n == 0 then Leaf else Node (tree (n - 1)) n (tree (n - 1))

fn numbers n acc -> r : n~Nat, acc~List Int, r~List Int
    decreasing n
    if n == 0 then acc else numbers (n - 1) (n :: acc)

fn tree_sum t -> s : t~Tree Int, s~Int
    match t
        Leaf       -> 0
        Node l x r -> tree_sum l + x + tree_sum r

fn list_sum xs acc -> s : xs~List Int, acc~Int, s~Int
    match xs
        []        -> acc
        x :: rest -> list_sum rest (acc + x)

# ── Generic: `k` times, each element one more ──

fn bump t k -> r : Mappable f, t~f Int, k~Nat, r~f Int
    decreasing k
    if k == 0 then t else bump (mapping (\x -> x + 1) t) (k - 1)

# ── Written for each type ──

fn map_tree g t -> r : g~(Int -> Int), t~Tree Int, r~Tree Int
    match t
        Leaf       -> Leaf
        Node l x r -> Node (map_tree g l) (g x) (map_tree g r)

fn bump_tree t k -> r : t~Tree Int, k~Nat, r~Tree Int
    decreasing k
    if k == 0 then t else bump_tree (map_tree (\x -> x + 1) t) (k - 1)

fn map_list g xs -> r : g~(Int -> Int), xs~List Int, r~List Int
    match xs
        []        -> []
        x :: rest -> g x :: map_list g rest

fn bump_list xs k -> r : xs~List Int, k~Nat, r~List Int
    decreasing k
    if k == 0 then xs else bump_list (map_list (\x -> x + 1) xs) (k - 1)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    let t = tree 16
    let xs = numbers 100000 []
    let (a, b) = match args
        ["mono"] -> (tree_sum (bump_tree t 40), list_sum (bump_list xs 40) 0)
        _        -> (tree_sum (bump t 40), list_sum (bump xs 40) 0)
    terminal.print_line format"{a} {b}" term
    Success
