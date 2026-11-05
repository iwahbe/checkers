module datatype_sorts

# Prover regression: a datatype nested inside other parametric datatypes
# (`List (String, Tree)`), and `Option` used at two sorts in one query.
# Both once made Z3 reject the query; an answer after a rejected command is
# never trusted.

enum Tree
    Leaf n      : n~Nat
    Node kids   : kids~List (String, Tree)

fn first_nat o -> n : o~Option Nat, n~Nat
    match o
        None   -> 0
        Some k -> k

fn first_tree o -> n : o~Option Tree, n~Nat
    match o
        None          -> 0
        Some (Leaf k) -> k
        Some (Node _) -> 1

fn both a b -> n : a~Option Nat, b~Option Tree, n~Nat, n >= first_nat a
    first_nat a + first_tree b

fn wrong a b -> n : a~Option Nat, b~Option Tree, n~Nat, n > first_nat a
    first_nat a + first_tree b
