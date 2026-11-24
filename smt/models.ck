# models.ck — Z3's models in the corpus, checked with `smt.model`.
#
# `main models DIR…` takes every query in each DIR (`H.smt2`) that Z3
# answered `sat` (`H.z3`, SPEC §7.2), reads the values Z3 printed for the
# query's `(get-value …)` terms into a `Model` (`answer.model_of`), and
# evaluates each of the query's assertions in it: the context's facts must
# be true and the goal false (the query asserts it negated).
#
# Definitions are run as their own bodies (`model.eval_unfolding`), each
# taken as terminating: `ckc` gives Z3 a definition only in a form whose
# recursion ends on every input (D118), and SMT-LIB can't say so in the
# query yet (#299). The summary says how many of the queries that hold have
# definitions.
#
# Each query is counted once, in the first of these that applies:
#
# - no `(get-value …)`: Z3 printed no values;
# - the query or Z3's answer doesn't read (listed, with why);
# - a `forall` without `:pattern`, or with one: `smt.model` can't evaluate
#   a quantifier over an infinite sort, so these are not checked;
# - an assertion is false (listed, with which): Z3's model is not a model;
# - all assertions hold;
# - not determined by what Z3 printed: an assertion needs a value Z3 didn't
#   print, or something `smt.model` doesn't decide; counted by the first
#   such reason. These are never counted as holding.
#
# `main model QUERY ANSWER` evaluates one query's assertions in the model
# of one answer, and says for each whether it holds, fails, or why it isn't
# determined.

module models

import std.files
import std.files (Fs, Entry)
import std.terminal (Term)
import std.string
import std.bytes
import std.list
import smtlib (Query, SExpr)
import term (Context, Command, DefineFuns, Def, Axiom, Head, Fun, Prim, Sel, Div, Mod, SeqNth, Select)
import model (Value, Truth, Unknown, NotGiven, OutOfFuel, ArraysCompared, NotTerminating, WrongSort, IllSorted)
import answer (Verdict, Sat, Unsat, GaveUp, Other)

# How many levels evaluation may go down: definitions' recursion and
# `lambda`s (`smt.model`).
let FUEL = 2000

# What checking one query found.
enum Outcome
    NoValues
    QueryUnread why       : why~Bytes
    AnswerUnread why      : why~Bytes
    Unpatterned
    Patterned
    Fails what            : what~Bytes
    Holds defs            : defs~Bool
    Undetermined kind why : kind~Bytes, why~Bytes
    # `refutes` disagrees with the assertions checked one by one: a bug in
    # this command or in `smt.model`.
    Disagrees

# `c` with every definition marked terminating.
fn marked c -> r : c~Context, r~Result Context Bytes
    match term.context (list.map mark (term.commands c))
        Ok d  -> Ok d
        Err _ -> Err b"the context with its definitions marked doesn't check"

fn mark cmd -> r : cmd~Command, r~Command
    match cmd
        DefineFuns s ds -> DefineFuns s (list.map (\d -> Def d.name d.params d.result d.body True) ds)
        other           -> other

fn unpatterned xs -> r : xs~List Axiom, r~Bool
    match xs
        []        -> False
        a :: rest -> a.patterns == [] or unpatterned rest

# Why a term has no value, in words; `kind` leaves out the names, to count
# reasons by.
fn reason c u kind -> r : c~Context, u~Unknown, kind~Bool, r~Bytes
    match u
        NotGiven (Fun f)       ->
            let funs = (term.signature c).funs
            if f >= len funs
                b"an undeclared function"
            else if kind
                if funs[f].params == [] then b"a constant Z3 didn't print" else b"a function with parameters, which Z3 doesn't print"
            else
                b"Z3 didn't print `" ++ funs[f].name ++ (if funs[f].params == [] then b"`" else b"` at these arguments")
        NotGiven (Prim Div)    -> b"a division by zero: Z3 didn't print its value"
        NotGiven (Prim Mod)    -> b"a remainder by zero: Z3 didn't print its value"
        NotGiven (Prim SeqNth) -> b"`seq.nth` out of range: Z3 didn't print its value"
        NotGiven (Sel _ _ _)   -> b"a selector of another constructor's value: Z3 didn't print its value"
        NotGiven _             -> b"something Z3 didn't print"
        OutOfFuel              -> b"evaluation needed more levels than it may go down"
        ArraysCompared         -> b"two arrays compared, which `smt.model` doesn't decide"
        NotTerminating         -> b"a definition not marked terminating"
        WrongSort              -> b"a value Z3 printed isn't of its term's sort"
        IllSorted              -> b"a term that isn't well-sorted"

# How assertion `t` came out: holds (`want` is its value), fails, or not
# determined.
enum Came
    Right
    Wrong
    Open u : u~Unknown

fn came r want -> k : r~Result Value Unknown, want~Bool, k~Came
    match r
        Ok (Truth b) -> if b == want then Right else Wrong
        Ok _         -> Open IllSorted
        Err u        -> Open u

# The facts, numbered from `n`, and how each came out.
fn each_fact c m ts n -> r : c~Context, m~model.Model, ts~List term.Term, n~Nat, r~List (Nat, Came)
    match ts
        []        -> []
        t :: rest -> (n, came (model.eval_unfolding c m t) True) :: each_fact c m rest (n + 1)

fn first_wrong rs -> r : rs~List (Nat, Came), r~Option Nat
    match rs
        []              -> None
        (n, Wrong) :: _ -> Some n
        _ :: rest       -> first_wrong rest

fn first_open rs -> r : rs~List (Nat, Came), r~Option Unknown
    match rs
        []               -> None
        (_, Open u) :: _ -> Some u
        _ :: rest        -> first_open rest

# Check the query `src` against Z3's answer `z3`.
fn check_query src z3 -> o : src~Bytes, z3~Bytes, o~Outcome
    match smtlib.parse src
        Err e -> QueryUnread (smtlib.describe src e)
        Ok q  ->
            match q.values
                None    -> NoValues
                Some ts ->
                    match smtlib.read z3
                        Err e -> AnswerUnread (smtlib.describe z3 e)
                        Ok es ->
                            match answer.printed q.context ts es
                                Err why  -> AnswerUnread why
                                Ok pairs -> check_in q pairs

fn check_in q pairs -> o : q~Query, pairs~List (term.Term, Value), o~Outcome
    let axioms = term.axioms q.context
    if unpatterned axioms
        Unpatterned
    else if axioms != []
        Patterned
    else
        match marked q.context
            Err why -> QueryUnread why
            Ok c    ->
                let m = answer.model_of c pairs FUEL
                let facts = each_fact c m (term.facts c) 1
                let goal = came (model.eval_unfolding c m q.goal) False
                let all = facts ++ [(0, goal)]
                let verdict =
                    match first_wrong all
                        Some 0 -> Fails b"the goal is true"
                        Some n -> Fails (b"fact " ++ smtlib.numeral n ++ b" is false")
                        None   ->
                            match first_open all
                                Some u -> Undetermined (reason c u True) (reason c u False)
                                None   -> Holds (term.defs c != [])
                let held = match verdict
                    Holds _ -> True
                    _       -> False
                if held != model.refutes c q.goal m then Disagrees else verdict

# ── The corpus ───────────────────────────────────────────────────────────────

# Whether `name` ends with `suffix`.
fn ends_with name suffix -> r : name~String, suffix~Bytes, r~Bool
    let b = string.bytes name
    len b > len suffix and bytes.matches_at b (len b - len suffix) suffix

# `name` without its last three bytes (`.z3`).
fn stem name -> r : name~String, r~String
    let b = string.bytes name
    match string.from_utf8 (if len b >= 3 then bytes.slice b 0 (len b - 3) else b)
        Some s -> s
        None   -> name

# Every `sat` answer in `dirs`, checked; `None` if a directory or file can't
# be read.
fn in_dirs dirs io fs -> r : dirs~List String, io~Term, fs~Fs, r~Option (List (Bytes, Outcome))
    match dirs
        []          -> Some []
        dir :: rest ->
            match files.list dir fs
                Err e ->
                    let _ = terminal.eprint_line ("error: " ++ dir ++ ": " ++ files.describe e) io
                    None
                Ok es ->
                    match (each dir es io fs, in_dirs rest io fs)
                        (Some xs, Some ys) -> Some (xs ++ ys)
                        _                  -> None

fn each dir es io fs -> r : dir~String, es~List Entry, io~Term, fs~Fs, r~Option (List (Bytes, Outcome))
    match es
        []        -> Some []
        e :: rest ->
            if e.dir or not (ends_with e.name b".z3")
                each dir rest io fs
            else
                let base = dir ++ "/" ++ stem e.name
                let z3_path = dir ++ "/" ++ e.name
                match files.read z3_path fs
                    Err err ->
                        let _ = terminal.eprint_line ("error: " ++ z3_path ++ ": " ++ files.describe err) io
                        None
                    Ok z3   ->
                        if answer.verdict z3 != Sat
                            each dir rest io fs
                        else
                            let query_path = base ++ ".smt2"
                            match files.read query_path fs
                                Err err ->
                                    let _ = terminal.eprint_line ("error: " ++ query_path ++ ": " ++ files.describe err) io
                                    None
                                Ok src  ->
                                    match each dir rest io fs
                                        Some more -> Some ((string.bytes base, check_query src z3) :: more)
                                        None      -> None

fn count p xs -> n : p~(Outcome -> Bool), xs~List (Bytes, Outcome), n~Nat
    match xs
        []             -> 0
        (_, o) :: rest -> if p o then 1 + count p rest else count p rest

# The reasons of `xs` not determined, each with how many.
fn reasons xs acc -> r : xs~List (Bytes, Outcome), acc~List (Bytes, Nat), r~List (Bytes, Nat)
    match xs
        []                            -> acc
        (_, Undetermined w _) :: rest -> reasons rest (bump acc w)
        _ :: rest                     -> reasons rest acc

fn bump acc w -> r : acc~List (Bytes, Nat), w~Bytes, r~List (Bytes, Nat)
    match acc
        []             -> [(w, 1)]
        (v, n) :: rest -> if v == w then (v, n + 1) :: rest else (v, n) :: bump rest w

fn line n what -> r : n~Nat, what~Bytes, r~Bytes
    b"  " ++ smtlib.numeral n ++ b" " ++ what ++ b"\n"

fn listed xs -> r : xs~List (Bytes, Outcome), r~Bytes
    match xs
        []             -> b""
        (p, o) :: rest ->
            let here =
                match o
                    QueryUnread w  -> p ++ b".smt2: doesn't read: " ++ w ++ b"\n"
                    AnswerUnread w -> p ++ b".z3: doesn't read: " ++ w ++ b"\n"
                    Fails w        -> p ++ b": Z3's model is not a model: " ++ w ++ b"\n"
                    Disagrees      -> p ++ b": `refutes` disagrees with the assertions one by one\n"
                    _              -> b""
            here ++ listed rest

fn reason_lines rs -> r : rs~List (Bytes, Nat), r~Bytes
    match rs
        []             -> b""
        (w, n) :: rest -> b"      " ++ smtlib.numeral n ++ b": " ++ w ++ b"\n" ++ reason_lines rest

fn is_no_values o -> r : o~Outcome, r~Bool
    match o
        NoValues -> True
        _        -> False

fn is_unread o -> r : o~Outcome, r~Bool
    match o
        QueryUnread _  -> True
        AnswerUnread _ -> True
        _              -> False

fn is_unpatterned o -> r : o~Outcome, r~Bool
    match o
        Unpatterned -> True
        _           -> False

fn is_patterned o -> r : o~Outcome, r~Bool
    match o
        Patterned -> True
        _         -> False

fn is_fails o -> r : o~Outcome, r~Bool
    match o
        Fails _ -> True
        _       -> False

fn is_holds o -> r : o~Outcome, r~Bool
    match o
        Holds _ -> True
        _       -> False

fn is_holds_defs o -> r : o~Outcome, r~Bool
    match o
        Holds True -> True
        _          -> False

fn is_open o -> r : o~Outcome, r~Bool
    match o
        Undetermined _ _ -> True
        _                -> False

fn is_disagrees o -> r : o~Outcome, r~Bool
    match o
        Disagrees -> True
        _         -> False

# The report on `xs`: the queries listed, then the counts.
export fn report xs -> r : xs~List (Bytes, Outcome), r~Bytes
    let n = \p -> count p xs
    listed xs ++ smtlib.numeral (list.length xs) ++ b" `sat` answers\n"
        ++ line (n is_no_values) b"without `(get-value …)`: no values printed"
        ++ line (n is_unread) b"whose query or answer doesn't read (listed above)"
        ++ line (n is_unpatterned) b"with a `forall` without `:pattern`: not checked"
        ++ line (n is_patterned) b"with only `forall`s with `:pattern`: not checked"
        ++ line (n is_fails) b"with an assertion false in Z3's model (listed above)"
        ++ line (n is_holds) b"where every assertion holds"
        ++ b"      (" ++ smtlib.numeral (n is_holds_defs) ++ b" of them with definitions, taken as terminating)\n"
        ++ line (n is_open) b"not determined by what Z3 printed, by the first reason:"
        ++ reason_lines (reasons xs [])
        ++ line (n is_disagrees) b"where `refutes` disagrees (listed above)"

# `main models DIR…`.
export fn run dirs io fs -> ok : dirs~List String, io~Term, fs~Fs, ok~Bool
    match in_dirs dirs io fs
        None    -> False
        Some xs ->
            let _ = terminal.write_bytes (report xs) io
            count is_unread xs == 0 and count is_fails xs == 0 and count is_disagrees xs == 0

# ── One query ────────────────────────────────────────────────────────────────

fn came_text c k -> r : c~Context, k~Came, r~Bytes
    match k
        Right  -> b"holds"
        Wrong  -> b"fails"
        Open u -> b"not determined: " ++ reason c u False

fn fact_lines c rs -> r : c~Context, rs~List (Nat, Came), r~Bytes
    match rs
        []             -> b""
        (n, k) :: rest -> b"fact " ++ smtlib.numeral n ++ b": " ++ came_text c k ++ b"\n" ++ fact_lines c rest

# `main model QUERY ANSWER`: each assertion of the query in the model of
# the answer (the model that knows nothing, if Z3 printed no values).
export fn one src z3 -> r : src~Bytes, z3~Bytes, r~Bytes
    let head = b"z3: " ++ verdict_text (answer.verdict z3) ++ b"\n"
    match smtlib.parse src
        Err e -> head ++ b"the query doesn't read: " ++ smtlib.describe src e ++ b"\n"
        Ok q  ->
            let pairs =
                match (answer.verdict z3, q.values)
                    (Sat, Some ts) ->
                        match smtlib.read z3
                            Ok es -> answer.printed q.context ts es
                            Err e -> Err (smtlib.describe z3 e)
                    _              -> Ok []
            match pairs
                Err why -> head ++ b"the answer doesn't read: " ++ why ++ b"\n"
                Ok ps   ->
                    match marked q.context
                        Err why -> head ++ why ++ b"\n"
                        Ok c    ->
                            let m = answer.model_of c ps FUEL
                            let goal = came (model.eval_unfolding c m q.goal) False
                            let axioms = term.axioms c
                            let note = if axioms == [] then b"" else b"a `forall`: not evaluated\n"
                            head ++ note ++ fact_lines c (each_fact c m (term.facts c) 1) ++ b"the negated goal: "
                                ++ came_text c goal ++ b"\n" ++ b"refutes: " ++ (if model.refutes c q.goal m then b"yes" else b"no")
                                ++ b"\n"

fn verdict_text v -> r : v~Verdict, r~Bytes
    match v
        Sat    -> b"sat"
        Unsat  -> b"unsat"
        GaveUp -> b"unknown"
        Other  -> b"no answer"
