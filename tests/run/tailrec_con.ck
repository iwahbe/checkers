# A constructor around a recursive call: the call runs in constant stack,
# and what the fields compute runs in the same order.
module tailrec_con

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.list (length)

fn build n -> r : n~Nat, r~List Nat
    if n == 0 then [] else n :: build (n - 1)

enum Tree
    Leaf
    Node l x r : l~Tree, x~Nat, r~Tree

# The call in a different field on each path.
fn insert x t -> r : x~Nat, t~Tree, r~Tree
    match t
        Leaf       -> Node Leaf x Leaf
        Node l y r -> if x < y then Node (insert x l) y r else Node l y (insert x r)

fn insert_all xs t -> r : xs~List Nat, t~Tree, r~Tree
    match xs
        []      -> t
        x :: ys -> insert_all ys (insert x t)

fn walk t -> r : t~Tree, r~List Nat
    match t
        Leaf       -> []
        Node l x r -> walk l ++ [x] ++ walk r

fn noisy n term -> r : n~Nat, term~Term, r~Nat
    terminal.print_line (format n) term
    n

enum Chain
    End
    Link rest x : rest~Chain, x~Nat

# A field after the call that does something: it runs after the call.
fn after n term -> r : n~Nat, term~Term, r~Chain
    if n == 0 then End else Link (after (n - 1) term) (noisy n term)

# A field before the call: it runs before.
fn before n term -> r : n~Nat, term~Term, r~List Nat
    if n == 0 then [] else noisy n term :: before (n - 1) term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (format (length (build 10000000))) term
    terminal.print_line (format (walk (insert_all [5, 2, 8, 1, 9, 3, 7] Leaf))) term
    terminal.print_line (format (after 3 term)) term
    terminal.print_line (format (before 3 term)) term
    Success
