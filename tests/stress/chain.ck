module chain

# Behaviours that schedule behaviours: each message to the actor sends the
# next one, 500 deep, and the last prints the trail, while 4 more actors count in parallel. Messages to
# one actor run in the order sent, so the trail is the same every time.

import system (System, ExitCode)
import actor (Actor)
import future (Future)
import terminal (Term)
import cown (Sched)
import list

fn step term k a sched x -> y : term~Term, k~Nat, a~Actor (List Nat), sched~Sched, x~List Nat, y~List Nat
    decreasing k
    if k == 0
        trail term x
    else
        actor.send a (\y -> step term (k - 1) a sched y) sched
        k :: x

fn add k n -> m : k~Nat, n~Nat, m~Nat
    n + k

fn count a k sched -> u : a~Actor Nat, k~Nat, sched~Sched, u~()
    decreasing k
    if k == 0
        ()
    else
        actor.send a (add k) sched
        count a (k - 1) sched

fn report term name x -> y : term~Term, name~String, x~a, y~a
    terminal.print_line (name ++ " " ++ format x) term
    x

fn first_three xs -> ys : xs~List Nat, ys~List Nat
    match xs
        a :: b :: c :: _ -> [a, b, c]
        _ -> xs

fn trail term xs -> ys : term~Term, xs~List Nat, ys~List Nat
    terminal.print_line ("trail " ++ format (list.length xs) ++ " " ++ format (first_three xs)) term
    xs

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term, sched } = sys
    let t = actor.new [] sched
    actor.send t (step term 500 t sched) sched
    let c1 = actor.new 0 sched
    let c2 = actor.new 0 sched
    count c1 300 sched
    count c2 300 sched
    actor.send c1 (report term "c1") sched
    actor.send c2 (report term "c2") sched
    future.ready Success
