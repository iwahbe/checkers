# One `join` for a future or a list of futures (D173): `s` says which, and in
# each arm of `match s` the types of `x` and `f` are refined to that case.
module join_shape

import std.future (Future)
import std.future
import std.cown (Sched)
import std.system (System, ExitCode)
import std.terminal

export enum Shape
    One
    Many

export fn futures s a -> t : s~Shape, a~Type, t~Type
    match s
        One  -> Future a
        Many -> List (Future a)

export fn values s a -> t : s~Shape, a~Type, t~Type
    match s
        One  -> a
        Many -> List a

# A future of every value, in order.
export fn all xs sched -> r : xs~own List (Future a), sched~Sched, r~Future (List a)
    match xs
        []        -> future.ready []
        x :: rest -> future.join (future.both x (all rest sched)) sched (\(v, vs) -> v :: vs)

export fn join s x sched f -> r : s~Shape, x~futures s a, sched~Sched, f~own (v~own values s a -> b),
                                  r~Future b
    match s
        One  -> future.join x sched f
        Many -> future.join (all x sched) sched f

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { sched, term } = sys
    let one = future.fork sched $ \_ ->
        20
    let many = [future.ready 1, future.fork sched (\_ -> 2), future.ready 3]
    let total = join Many many sched $ \vs ->
        terminal.print_line ("many: " ++ format vs) term
        len vs
    let both = future.both one total
    join One both sched $ \(n, k) ->
        terminal.print_line ("one: " ++ format n ++ ", count: " ++ format k) term
        Success
