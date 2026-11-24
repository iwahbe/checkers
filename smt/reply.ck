# reply.ck — our answer to a query, and how Z3 would write it.
#
# Until the solver exists, the answer to every query that reads is
# `Unknown`. `write` gives the answer in Z3's output format, so `main`
# can stand in for `z3 -in`: `unsat`, or `unknown`, then, if the query
# asks `(get-value …)`, the error Z3 gives when it has no model.

module reply

import std.list
import smtlib (Query, SExpr, Node, Leaf, Symbol)

# Why we give up on a query.
export enum GiveUp
    # There is no solver yet: every query is answered `Unknown`.
    NoSolver

# Our answer to a query: `Valid` if the goal follows from the context (Z3
# says `unsat`), `Unknown` if we can't tell.
export enum Answer
    Valid
    Unknown why : why~GiveUp

# What `why` is, in words.
export fn reason why -> r : why~GiveUp, r~Bytes
    match why
        NoSolver -> b"no solver yet"

# `why` as one word, for files that list rows.
export fn key why -> r : why~GiveUp, r~String
    match why
        NoSolver -> "no-solver"

# Our answer to `q`.
export fn answer q -> a : q~Query, a~Answer
    Unknown NoSolver

# Our answer to the query `src` reads as, written as Z3 writes its own.
# Z3 has no model to show after `unsat` or `unknown`, so a `(get-value …)`
# gets `(error "line L column C: model is not available")`, where L and C
# are those of the command's closing `)`, its column counted from 0.
export fn write src q a -> r : src~Bytes, q~Query, a~Answer, r~Bytes
    let verdict = match a
        Valid     -> b"unsat\n"
        Unknown _ -> b"unknown\n"
    match q.values
        None   -> verdict
        Some _ ->
            match get_value_end src
                None    -> verdict
                Some at ->
                    let (line, col) = smtlib.position src at
                    verdict ++ b"(error \"line " ++ smtlib.numeral line ++ b" column " ++ smtlib.numeral (col - 1)
                        ++ b": model is not available\")\n"

# Whether what `write` gives ends with an error: Z3 then exits with status 1.
export fn has_error q -> r : q~Query, r~Bool
    match q.values
        None   -> False
        Some _ -> True

# The offset of the closing `)` of the query's last command, if it is
# `(get-value …)`.
fn get_value_end src -> r : src~Bytes, r~Option (p~Nat, p < len src)
    match smtlib.read src
        Err _ -> None
        Ok es ->
            match list.reverse es
                Node (Leaf (Symbol n False) _ :: _) at :: _ if n == b"get-value" ->
                    match smtlib.end_of src at
                        Ok j  -> Some (j - 1)
                        Err _ -> None
                _ -> None
