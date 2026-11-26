# reply.ck — our answer to a query, and how Z3 would write it.
#
# Until the solver exists, the answer to every query that reads is
# `Unknown`. `write` gives the answer in Z3's output format, so `main`
# can stand in for `z3 -in`: `unsat` or `unknown`, then what Z3 writes for
# each command after `(check-sat)`: for `(get-unsat-core)`, the core or the
# error Z3 gives when it has none; for `(get-value …)`, the error Z3 gives
# when it has no model.

module reply

import smtlib (Query, Opt, Atom, SExpr, Node, Leaf, Symbol)
import term

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
#
# Z3 has no model to show after `unsat` or `unknown`, so a `(get-value …)`
# gets `(error "line L column C: model is not available")`, where L and C
# are those of the command's closing `)`, its column counted from 0.
#
# A `(get-unsat-core)` gets, as from Z3, an error at its closing `)` unless
# the query sets `(set-option :produce-unsat-cores true)` and the answer is
# `Valid`; then it gets the names of the query's assertions, all of them in
# the order written. That is a core, if not the smallest: the assertions
# contradict each other. (The names of the facts a certificate uses will
# be a smaller one, #86.)
export fn write src q a -> r : src~Bytes, q~Query, a~Answer, r~Bytes
    let verdict = match a
        Valid     -> b"unsat\n"
        Unknown _ -> b"unknown\n"
    match smtlib.read src
        Err _ -> verdict
        Ok es -> verdict ++ asked src q a (after_check_sat es)

# Whether what `write` gives holds an error: Z3 then exits with status 1.
export fn has_error q a -> r : q~Query, a~Answer, r~Bool
    q.values != None or (q.core and not (a == Valid and cores_on q.options))

# Whether the options ask for unsat cores: one sets `:produce-unsat-cores`
# to `true`. Z3 (5.3.3) keeps them on once asked, even if a later option sets
# it to `false`.
fn cores_on os -> r : os~List Opt, r~Bool
    match os
        []        -> False
        o :: rest -> (o.key == b"produce-unsat-cores" and is_true o.value) or cores_on rest

fn is_true v -> r : v~Atom, r~Bool
    match v
        Symbol t False -> t == b"true"
        _              -> False

# The commands after `(check-sat)`.
fn after_check_sat es -> r : es~List (SExpr src), r~List (SExpr src)
    match es
        []        -> []
        Node [Leaf (Symbol n False) _] _ :: rest if n == b"check-sat" -> rest
        _ :: rest -> after_check_sat rest

# What Z3 writes for each of `es`, commands after `(check-sat)`.
fn asked src q a es -> r : src~Bytes, q~Query, a~Answer, es~List (SExpr src), r~Bytes
    match es
        []        -> b""
        e :: rest -> one src q a e ++ asked src q a rest

fn one src q a e -> r : src~Bytes, q~Query, a~Answer, e~SExpr src, r~Bytes
    match e
        Node (Leaf (Symbol n False) _ :: _) at if n == b"get-unsat-core" ->
            if not (cores_on q.options)
                error_at src at b"unsat core construction is not enabled, use command (set-option :produce-unsat-cores true)"
            else if a == Valid
                b"(" ++ names (term.names q.context) ++ b")\n"
            else
                error_at src at b"unsat core is not available"
        Node (Leaf (Symbol n False) _ :: _) at if n == b"get-value" -> error_at src at b"model is not available"
        _ -> b""

# Names separated by spaces.
fn names ns -> r : ns~List term.Name, r~Bytes
    match ns
        []        -> b""
        [n]       -> smtlib.name_text n
        n :: rest -> smtlib.name_text n ++ b" " ++ names rest

# Z3's error for the command at `at`: at its closing `)`, the column counted
# from 0.
fn error_at src at message -> r : src~Bytes, at~Nat, at < len src, message~Bytes, r~Bytes
    match smtlib.end_of src at
        Err _ -> b""
        Ok j  ->
            let (line, col) = smtlib.position src (j - 1)
            b"(error \"line " ++ smtlib.numeral line ++ b" column " ++ smtlib.numeral (col - 1) ++ b": " ++ message ++ b"\")\n"
