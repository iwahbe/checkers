# Recursion through a function that promises, in its signature, to call its
# function argument only with elements of a list (#102).
module termination_containers

import std.list

enum Tree
    Leaf
    One kid   : kid~Tree
    Many kids : kids~List Tree

# `list.all p xs` calls `p` only with elements of `xs`.
fn walk t -> r : t~Tree, r~Bool
    match t
        Leaf      -> True
        One kid   -> walk kid
        Many kids -> list.all walk kids

# A partial application: its remaining parameter gets the element.
fn by_partial k t -> r : k~Nat, t~Tree, r~Nat
    match t
        Leaf      -> k
        One kid   -> by_partial k kid
        Many kids -> list.max_of (list.map (by_partial k) kids)

# A lambda: its parameter is the element.
fn by_lambda t -> r : t~Tree, r~Bool
    match t
        Leaf      -> True
        One kid   -> by_lambda kid
        Many kids -> list.all (\k -> by_lambda k) kids

# A program's own function with the same promise.
fn each xs p -> r : xs~List a, p~(x~a -> Bool, list.contains xs x), r~Bool
    match xs
        []        -> True
        x :: rest -> p x and each rest p

fn by_own t -> r : t~Tree, r~Bool
    match t
        Leaf      -> True
        One kid   -> by_own kid
        Many kids -> each kids by_own

# Without the promise, the element isn't known to be part of `t`.
fn every xs p -> r : xs~List a, p~(a -> Bool), r~Bool
    match xs
        []        -> True
        x :: rest -> p x and every rest p

fn by_unpromised t -> r : t~Tree, r~Bool
    match t
        Leaf      -> True
        One kid   -> by_unpromised kid
        Many kids -> every kids by_unpromised

check walk (Many [One Leaf, Leaf])
check by_partial 1 (Many [Leaf]) == 1
