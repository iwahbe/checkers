# One function for a future or a list of futures (#664): `s` says which, and
# in each arm of `match s` the types of `x` and the result are refined to
# that case.
module join_shape

import std.future (Future)
import std.future
import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

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

# Every value, in order.
export fn all xs -> r : xs~List (Future a), r~List a
    match xs
        []        -> []
        x :: rest -> future.join x :: all rest

export fn join s x -> r : s~Shape, x~futures s a, r~values s a
    match s
        One  -> future.join x
        Many -> all x

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { sched, term } = sys
    let one = future.fork sched $ \_ ->
        20
    let many = [future.ready 1, future.fork sched (\_ -> 2), future.ready 3]
    let vs = join Many many
    terminal.print_line ("many: " ++ debug vs) term
    let n = join One one
    terminal.print_line ("one: " ++ debug n ++ ", count: " ++ debug (len vs)) term
    Success
