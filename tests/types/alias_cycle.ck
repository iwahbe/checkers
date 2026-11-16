module alias_cycle

# An alias stands for its definition, so one that needs itself through
# aliases alone never ends (E0225); a type contains itself only through an
# `enum` or a `record`.

type A = x~B
type B = x~A

type Nested = x~List Nested

enum Tree
    Node kids : kids~Forest
type Forest = x~List Tree

fn size t -> n : t~Tree, n~Nat
    match t
        Node kids -> list_size kids

fn list_size ts -> n : ts~Forest, n~Nat
    match ts
        []        -> 0
        t :: rest -> 1 + size t + list_size rest

check size (Node [Node [], Node []]) == 2
