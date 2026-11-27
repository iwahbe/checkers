# reply.ck — our answer to a query, and how Z3 would write it.
#
# Our answer is `smt.solve`'s: `Valid` only with a refutation
# `cert.checks` accepted, otherwise `Unknown` with why. (`solve` never
# answers `Invalid` yet, #86; writing a model for `sat` comes with it.)
# `write` gives the answer in Z3's output format, so `main`
# can stand in for `z3 -in`: `unsat` or `unknown`, then what Z3 writes for
# each command after `(check-sat)`: for `(get-unsat-core)`, the core or the
# error Z3 gives when it has none; for `(get-value …)`, the error Z3 gives
# when it has no model.

module reply

import smtlib (Query, Opt, Atom, SExpr, Node, Leaf, Symbol)
import term
import std.string
import solve (Limits, OutOfWork, Unsupported, Incomplete, Proved, Refuted, GaveUp)

# Why we give up on a query: `smt.solve`'s reason.
export type Reason = g~solve.GiveUp

# Our answer to a query: `Valid` if the goal follows from the context (Z3
# says `unsat`), `Unknown` if we can't tell.
export enum Answer
    Valid
    Unknown why : why~Reason

# What `why` is, in words.
export fn reason why -> r : why~Reason, r~Bytes
    match why
        OutOfWork        -> b"out of work"
        Unsupported what -> b"unsupported: " ++ string.bytes what
        Incomplete       -> b"no refutation by unit propagation"

# `why` as one word, for files that list rows.
export fn key why -> r : why~Reason, r~String
    match why
        OutOfWork     -> "out-of-work"
        Unsupported _ -> "unsupported"
        Incomplete    -> "incomplete"

# The work `solve` may do on one query (clauses looked at).
let LIMITS = Limits 1000000

# Our answer to `q`, and the work it took.
export fn solved q -> r : q~Query, r~(Answer, Nat)
    let out = solve.solve (solve.prepare q.context) q.goal LIMITS
    match solve.verdict out.answer
        Proved     -> (Valid, out.work)
        # Not yet: `solve` gives no counterexamples (#86). `sat` will need
        # the model written for `(get-value …)`.
        Refuted    -> (Unknown (Unsupported "writing a counterexample"), out.work)
        GaveUp why -> (Unknown why, out.work)

# Our answer to `q`.
export fn answer q -> a : q~Query, a~Answer
    let (a, _) = solved q
    a

# Our answer to the query `src` reads as, written as Z3 writes its own.
#
# `main` has no model to show after its `unsat` or `unknown`, so a
# `(get-value …)` gets Z3's error for that case, `(error "line L column C:
# model is not available")`, where L and C are as Z3 gives those of the
# command's closing `)` (`z3_column`). (Z3 itself may show a model after
# `unknown`; `main` has none.)
#
# A `(get-unsat-core)` gets, as from Z3, an error at its closing `)` unless
# the query sets `(set-option :produce-unsat-cores true)` and the answer is
# `Valid`; then it gets the names of the query's assertions, all of them in
# the order written. That is a core, if not the smallest: the assertions
# contradict each other. (The names of the facts a certificate uses will
# be a smaller one, #86.) It needn't be Z3's text once `Valid` is reached:
# the comparison must then compare a core as a core, not as text.
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

# Whether the options ask for unsat cores (`:produce-unsat-cores true`).
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

# Z3's error for the command at `at`: at its closing `)`.
fn error_at src at message -> r : src~Bytes, at~Nat, at < len src, message~Bytes, r~Bytes
    match smtlib.end_of src at
        Err _ -> b""
        Ok j  ->
            let (line, _) = smtlib.position src (j - 1)
            let col = z3_column src (j - 1)
            b"(error \"line " ++ smtlib.numeral line ++ b" column " ++ smtlib.numeral col ++ b": " ++ message ++ b"\")\n"

# The column Z3 (5.3.3) gives byte `pos`: its offset in its line, counted
# from 0, and one more on the first line and on a line that starts inside a
# quoted symbol (measured; a line starting inside a comment doesn't).
fn z3_column src pos -> r : src~Bytes, pos~Nat, pos <= len src, r~Nat
    let (start, extra) = line_start src 0 pos False False 0 1
    pos - start + extra

# Where the line holding `pos` starts, and whether it is one more, reading
# from `i`: `bar` and `comment` say whether `i` is inside a quoted symbol or
# a comment, `start` and `extra` are so far.
fn line_start src i pos bar comment start extra -> r : src~Bytes, i~Nat, pos~Nat, i <= pos, pos <= len src, bar~Bool,
                                                       comment~Bool, start~Nat, start <= i, extra~Nat,
                                                       r~((s~Nat, s <= pos), Nat)
    decreasing pos - i
    if i >= pos
        (start, extra)
    else
        let b = src[i]
        if b == '\n'
            line_start src (i + 1) pos bar False (i + 1) (if bar then 1 else 0)
        else if comment
            line_start src (i + 1) pos bar True start extra
        else if b == '|'
            line_start src (i + 1) pos (not bar) False start extra
        else if b == ';' and not bar
            line_start src (i + 1) pos bar True start extra
        else
            line_start src (i + 1) pos bar False start extra
