# In a group that isn't shown to terminate, E0301 points at the call where
# the cycle loses the parameter it recursed on, not at one that passes a
# parameter, or a part of one, on.
module termination_group_span

enum Tree
    Leaf
    Node kids : kids~List Tree

# `walk` passes a part of `t` and `walk_all` a part of `ts`; `through` passes
# a new list, so it is `through` that loses it.
fn walk t -> r : t~Tree, r~Nat
    match t
        Leaf      -> 1
        Node kids -> through kids

fn through kids -> r : kids~List Tree, r~Nat
    walk_all (Leaf :: kids)

fn walk_all ts -> r : ts~List Tree, r~Nat
    match ts
        []        -> 0
        t :: rest -> walk t + walk_all rest

# `keep` passes its parameter on unchanged; `lose` passes something bigger.
fn keep t -> r : t~Tree, r~Nat
    lose t

fn lose t -> r : t~Tree, r~Nat
    match t
        Leaf   -> 0
        Node _ -> keep (Node [t])

# The same with a number: no measure is shown smaller at `up (n + 1)`.
fn same n -> r : n~Nat, r~Nat
    up n

fn up n -> r : n~Nat, r~Nat
    if n == 0 then 0 else same (n + 1)
