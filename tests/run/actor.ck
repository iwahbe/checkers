module actor_demo

# An account actor whose balance never goes negative; messages run in order.

import system (System, ExitCode)
import actor (Actor)
import future (Future)
import terminal (Term)

type Balance = n~Nat

fn deposit k b -> r : k~Nat, b~Balance, r~Balance
    b + k

fn withdraw k b -> r : k~Nat, b~Balance, r~Balance
    if k <= b then b - k else b

fn report term b -> r : term~Term, b~Balance, r~Balance
    terminal.print_line ("balance " ++ format b) term
    b

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { term, sched } = sys
    let acct = actor.new 10 sched
    actor.send acct (deposit 5) sched
    actor.send acct (withdraw 30) sched
    actor.send acct (withdraw 12) sched
    actor.send acct (report term) sched
    future.ready Success
