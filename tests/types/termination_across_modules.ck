# Recursion through another module's function: read from its body when it is
# exported `transparent`, else from its signature.
module termination_across_modules

import containers.each

enum Tree
    Leaf
    Many kids : kids~List Tree

fn by_shown t -> r : t~Tree, r~Bool
    match t
        Leaf      -> True
        Many kids -> each.shown kids by_shown

fn by_promised t -> r : t~Tree, r~Bool
    match t
        Leaf      -> True
        Many kids -> each.promised kids by_promised

fn by_hidden t -> r : t~Tree, r~Bool
    match t
        Leaf      -> True
        Many kids -> each.hidden kids by_hidden
