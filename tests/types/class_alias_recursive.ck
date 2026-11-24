module class_alias_recursive

# A class used at a refinement alias whose function gives values of the
# class's type under a recursive type (`List t`, `Tree t`): the instance's
# signature must promise they are of the alias, by its type (`Tree Nat`)
# or, for a list, with `list.all`. `Bare`'s and `Loose`'s don't.

import std.list

enum Tree a : a~Type
    Leaf
    Node l x r : l~Tree a, x~a, r~Tree a

class Grow t
    fn grow n -> r : n~Int, r~Tree t

instance Grow Int
    fn grow n -> r : n~Int, r~Tree Nat
        Leaf

class Several t
    fn several n -> r : n~Nat, r~List t

instance Several Int
    fn several n -> r : n~Nat, r~List Int, list.all (\x -> x >= 0) r
        have none
        []

class Loose t
    fn loose n -> r : n~Int, r~List t

instance Loose Int
    fn loose n -> r : n~Int, r~List Int, list.all (\x -> x >= -1) r
        have none
        []

class Bare t
    fn bare n -> r : n~Int, r~Tree t

instance Bare Int
    fn bare n -> r : n~Int, r~Tree Int
        Node Leaf n Leaf

# `list.all` is sealed: what an empty list satisfies is assumed here.
lemma none
    ensures list.all (\x -> x >= 0) [] and list.all (\x -> x >= -1) []
    proof
        admit

fn by_type -> t : t~Tree Nat
    grow 1

fn by_all -> xs : xs~List Nat
    several 3

fn generic -> xs : Several t, xs~List t
    several 2

fn through_dictionary -> xs : xs~List Nat
    generic

fn by_type_wrong -> t : t~Tree Nat
    bare (-1)

fn by_all_wrong -> xs : xs~List Nat
    loose 1

fn loose_generic -> xs : Loose t, xs~List t
    loose 2

fn through_dictionary_wrong -> xs : xs~List Nat
    loose_generic
