# Recursion is structural when every cycle of calls, taken together, makes
# some parameter strictly smaller: a call may pass a parameter on as it is.
module termination_size_change

enum Tree
    Leaf
    Node kids : kids~List Tree

enum Peano
    Zero
    Succ p : p~Peano

# `through` passes its parameter on unchanged; around the cycle `walk` →
# `through` → `walk_all` → `walk`, `t` gets smaller.
fn walk t -> r : t~Tree, r~Nat
    match t
        Leaf      -> 1
        Node kids -> through kids

fn through kids -> r : kids~List Tree, r~Nat
    walk_all kids

fn walk_all ts -> r : ts~List Tree, r~Nat
    match ts
        []        -> 0
        t :: rest -> walk t + walk_all rest

check walk (Node [Leaf, Leaf]) == 2

# The arguments change places: every second call, both are smaller.
fn swap a b -> r : a~Peano, b~Peano, r~Nat
    match a
        Zero   -> 0
        Succ p -> 1 + swap b p

check swap (Succ (Succ Zero)) (Succ Zero) == 3

# Lexicographic: `a` gets smaller, or stays and `b` does.
fn lex a b -> r : a~Peano, b~Peano, r~Nat
    match a
        Zero   -> 0
        Succ p ->
            match b
                Zero   -> 1 + lex p (Succ Zero)
                Succ q -> lex a q + lex p b

check lex (Succ Zero) (Succ Zero) == 1

# Around `spin` → `spin_all` → `spin`, nothing is smaller.
fn spin t -> r : t~Tree, r~Nat
    match t
        Leaf      -> 0
        Node kids -> spin_all kids

fn spin_all ts -> r : ts~List Tree, r~Nat
    match ts
        []        -> 0
        _ :: rest -> spin (Node rest)

# Neither argument gets smaller.
fn flip a b -> r : a~Peano, b~Peano, r~Nat
    match a
        Zero   -> 0
        Succ _ -> flip b a
