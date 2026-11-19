# Recursion through a function that calls its function argument only with
# elements of a list: promised in its signature, or shown by its body.
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

# A function of the same module needs no promise: its body shows it calls
# `p` only with elements of `xs`.
fn every xs p -> r : xs~List a, p~(a -> Bool), r~Bool
    match xs
        []        -> True
        x :: rest -> p x and every rest p

fn by_body t -> r : t~Tree, r~Bool
    match t
        Leaf      -> True
        One kid   -> by_body kid
        Many kids -> every kids by_body

# Through another function of the module that keeps the promise.
fn every_twice xs p -> r : xs~List a, p~(a -> Bool), r~Bool
    every xs p and list.all p xs

fn by_two t -> r : t~Tree, r~Bool
    match t
        Leaf      -> True
        One kid   -> by_two kid
        Many kids -> every_twice kids by_two

# `p` is also called with `extra`, which isn't a part of `xs`.
fn with_extra extra xs p -> r : extra~a, xs~List a, p~(a -> Bool), r~Bool
    p extra and every xs p

fn by_extra t -> r : t~Tree, r~Bool
    match t
        Leaf      -> True
        One kid   -> by_extra kid
        Many kids -> with_extra t kids by_extra

# `f` is returned: what it is called with isn't known.
fn hold f xs -> r : f~a, xs~List b, r~a
    f

fn by_hold t -> r : t~Tree, r~Bool
    match t
        Leaf      -> True
        One kid   -> by_hold kid
        Many kids -> (hold by_hold kids) t

check walk (Many [One Leaf, Leaf])
check by_partial 1 (Many [Leaf]) == 1
