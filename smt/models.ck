# models.ck — Z3's models of the corpus's queries, checked with `smt.model`.
#
# `main models DIR…` accounts for every file in each DIR: each query
# (`H.smt2`) with its answer (`H.z3`, SPEC §7.2); a query without an
# answer, an answer without a query, and any other file are listed and
# fail the run. For each query Z3 answered `sat`, it reads the values Z3
# printed for the query's `(get-value …)` terms into a `Model`
# (`answer.model_of`), and evaluates each of the query's assertions in it:
# the context's facts must be true and the goal false (the query asserts
# it negated).
#
# `main models --z3 PROGRAM DIR…` asks for the whole model instead: for each
# of those queries it runs `PROGRAM -in` (as `main compare` runs Z3) on the
# query with `(get-model)` after it, and reads what Z3 prints
# (`z3model.model_of`). Z3's full model leaves out only two things: the
# query's definitions with parameters, which are run as their bodies, and
# the values of a selector applied to another constructor's value, which
# `get-model` doesn't print. The constants the query defines it prints
# with their values, and each must be what the definition gives. It needs
# a `z3` executable (Z3 5.3.3), so `cargo test` doesn't run it.
#
# Definitions are run as their own bodies (`model.eval_unfolding`) only
# when taken as terminating, and nothing here takes one so by itself: SMT-LIB
# can't say a definition terminates, so the caller says it, with
# `--terminating`, for every definition, and the output says it was
# given. (`ckc` gives Z3 a definition only in a form whose recursion ends on
# every input, so the corpus scripts and golden tests pass it.) Without it a
# call of a definition is not determined. The summary says how many of the
# queries that hold have definitions, and how many a `lambda`, which
# `model.refutes` refuses.
#
# Each query is counted once, in the first of these that applies:
#
# - Z3 answered `unsat` or `unknown`: there is no model to check;
# - with `--z3`, Z3 run now doesn't answer `sat` (listed);
# - no `(get-value …)` (without `--z3`): Z3 printed no values;
# - the query, the answer or the model doesn't read (listed, with why):
#   an answer whose first line isn't exactly `sat`, `unsat` or `unknown`
#   is one of these;
# - an assertion without a quantifier is false (listed, with which): Z3's
#   model is not a model;
# - a `forall` without `:pattern`, or with one: `smt.model` can't evaluate
#   a quantifier over an infinite sort, so these are not checked further;
# - all assertions hold;
# - not determined by what Z3 printed: an assertion needs a value Z3 didn't
#   print, or something `smt.model` doesn't decide; counted by the first
#   such reason. These are never counted as holding.
#
# With `--z3`, a query that asks `(get-value …)` gets that list and then
# the model. Both are read: the list with the model's universes, and each
# value must be what the model gives its term wherever the model
# determines it (a value through `(div x 0)` the model doesn't print is
# not compared). The values Z3 prints for the query's own constants and
# named assertions must be what the query gives them, or the run fails.
#
# `main model [--terminating] QUERY ANSWER` evaluates one query's
# assertions in the model of one answer (what `(get-model)` printed, if the
# answer ends with it; else the `(get-value …)` values), and says for each
# whether it holds, fails, or why it isn't determined, and whether
# `model.refutes` takes the model.

module models

import std.files
import std.files (Fs, Entry)
import std.proc
import std.system (Proc)
import std.terminal (Term)
import std.string
import std.bytes
import std.list
import smtlib (Query, SExpr, Leaf, Node, Symbol)
import term (Name, Context, Command, DefineFuns, Def, Axiom, Head, Fun, Prim, Sel, ConstArr, Div, Mod, SeqNth, Select, Store, MapAdd, Recursive, Plain, App)
import model (Value, Truth, Unknown, NotGiven, LambdaNotGiven, OutOfFuel, NotTerminating, WrongSort, IllSorted)
import answer (Verdict, Sat, Unsat, GaveUp, Other)
import z3model
import printed

# How many levels evaluation may go down: definitions' recursion and
# `lambda`s (`smt.model`).
let FUEL = answer.FUEL

# What checking one query found.
enum Outcome
    NoValues
    # Z3 answered `unsat` or `unknown` (`v`): there is no model to check.
    Answered v            : v~Bytes
    # A file that is neither a query nor an answer, in a directory given.
    Stray what            : what~Bytes
    # The query introduces a name with `!`, as Z3's own names are: its
    # answer is not read.
    BangUnread
    QueryUnread why       : why~Bytes
    AnswerUnread why      : why~Bytes
    Unpatterned
    Patterned
    Fails what            : what~Bytes
    Holds defs lambda     : defs~Bool, lambda~Bool
    Undetermined kind why : kind~Bytes, why~Bytes
    # `--z3`: Z3 run now doesn't answer `sat` (it answered `v`).
    NowAnswers v          : v~Bytes
    # `--z3`: the program can't be run (`why`).
    NotRun why            : why~Bytes
    # `--z3`: Z3's `(get-model)` output doesn't read, or holds a form this
    # reader doesn't know.
    ModelUnread why       : why~Bytes
    # `refutes` disagrees with the assertions checked one by one: a bug in
    # this command or in `smt.model`.
    Disagrees

# `c` with every definition marked terminating.
export fn marked c -> r : c~Context, r~Result Context Bytes
    match term.context (list.map mark (term.commands c))
        Ok d  -> Ok d
        Err _ -> Err b"the context with its definitions marked doesn't check"

fn mark cmd -> r : cmd~Command, r~Command
    match cmd
        DefineFuns s ds -> DefineFuns s (list.map (\d -> Def d.name d.params d.result d.body True d.kind) ds)
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
        NotGiven (Prim Select) -> b"an array Z3 printed, at an index it doesn't say"
        NotGiven (Prim Store)  -> printed.NO_NORMAL_FORM
        NotGiven (Prim MapAdd) -> printed.NO_NORMAL_FORM
        NotGiven (ConstArr _)  -> printed.NO_NORMAL_FORM
        NotGiven _             -> b"something Z3 didn't print"
        LambdaNotGiven         -> b"a `lambda`, which has no normal form"
        OutOfFuel              -> b"evaluation needed more levels than it may go down"
        NotTerminating         -> b"a definition, not taken as terminating (`--terminating` takes it so)"
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
fn check_query t src z3 -> o : t~Bool, src~Bytes, z3~Bytes, o~Outcome
    match smtlib.parse src
        Err e -> QueryUnread (smtlib.describe src e)
        Ok q  ->
            match q.values
                None    -> NoValues
                Some ts ->
                    let text = if q.core then answer.without_core_error z3 src else z3
                    match (smtlib.read text, smtlib.read src, context_for t q)
                        (Err e, _, _)         -> AnswerUnread (smtlib.describe text e)
                        (_, Err e, _)         -> QueryUnread (smtlib.describe src e)
                        (_, _, Err w)         -> QueryUnread w
                        (Ok es, Ok qes, Ok c) ->
                            if z3model.bang q.context
                                BangUnread
                            else
                                match answer.printed c ts (answer.asked qes) es
                                    Err why  -> AnswerUnread why
                                    Ok pairs -> check_in t q pairs

# `q`'s context, with every definition marked terminating if `t`.
fn context_for t q -> r : t~Bool, q~Query, r~Result Context Bytes
    if t then marked q.context else Ok q.context

fn check_in t q pairs -> o : t~Bool, q~Query, pairs~List (term.Term, Value), o~Outcome
    let asked = asked_terms q
    check_with t q (\c -> answer.model_of c [] pairs FUEL) [] (\c u -> (values_reason c asked pairs u True, values_reason c asked pairs u False))

fn asked_terms q -> r : q~Query, r~List term.Term
    match q.values
        Some ts -> ts
        None    -> []

# Why a term isn't determined by the values printed for `asked` (`pairs`):
# a constant asked for whose printed value has no normal form is printed,
# not left out.
fn values_reason c asked pairs u kind -> r : c~Context, asked~List term.Term, pairs~List (term.Term, Value), u~Unknown,
                                             kind~Bool, r~Bytes
    match u
        NotGiven (Fun f) ->
            if list.contains asked (App (Fun f) []) and not (list.contains (list.map (\(t, _) -> t) pairs) (App (Fun f) []))
                if kind then printed.NO_NORMAL_FORM else b"Z3 printed `" ++ name_of (term.signature c) f ++ b"`: " ++ printed.NO_NORMAL_FORM
            else
                reason c u kind
        _                -> reason c u kind

# Check `q`'s assertions in the model `make` gives for its context, with
# its definitions marked terminating if `terminating`, and that each of
# `own` (a term of the query's and the value Z3 printed for it) is that
# value there when determined; `why` says why a term isn't determined (a
# kind to count by, and the details).
fn check_with terminating q make printed_own why -> o : terminating~Bool, q~Query, make~(Context -> model.Model),
                                                        printed_own~List (Name, term.Term, Option Value), why~(Context -> Unknown -> (Bytes, Bytes)),
                                                        o~Outcome
    match (if terminating then marked q.context else Ok q.context)
        Err w -> QueryUnread w
        Ok c  ->
            let m = make c
            let facts = each_fact c m (term.facts c) 1
            let goal = came (model.eval_unfolding c m q.goal) False
            let all = facts ++ [(0, goal)]
            let axioms = term.axioms c
            match (first_wrong all, first_other c m printed_own)
                (Some 0, _)    -> Fails b"the goal is true"
                (Some n, _)    -> Fails (b"fact " ++ smtlib.numeral n ++ b" is false")
                (None, Some n) -> Fails (b"Z3 printed a value for `" ++ n ++ b"` that the query doesn't give it")
                (None, None)   ->
                    if unpatterned axioms
                        Unpatterned
                    else if axioms != []
                        Patterned
                    else
                        let lambda = not (model.without_lambda c q.goal)
                        let verdict =
                            match first_open all
                                Some u ->
                                    let (kind, detail) = why c u
                                    Undetermined kind detail
                                None   -> Holds (term.defs c != []) lambda
                        # `refutes` takes a model where every assertion holds, unless
                        # there is a `lambda` or an unmarked definition.
                        let refutable =
                            match verdict
                                Holds _ False -> model.defs_run c
                                _             -> False
                        if refutable != model.refutes c q.goal m then Disagrees else verdict

# The first of the printed values of the query's own constants and named
# assertions whose term evaluates in `m` to another value.
fn first_other c m printed_own -> r : c~Context, m~model.Model, printed_own~List (Name, term.Term, Option Value), r~Option Name
    match printed_own
        []                     -> None
        (n, t, Some v) :: rest ->
            match model.eval_unfolding c m t
                Ok w  -> if w != v then Some n else first_other c m rest
                Err _ -> first_other c m rest
        (_, _, None) :: rest   -> first_other c m rest

# ── Asking Z3 ────────────────────────────────────────────────────────────────

# Why a term isn't determined in the model Z3's `(get-model)` printed: what
# Z3 leaves out of it, or what it printed and this reader couldn't evaluate.
fn z3_reason full c u -> r : full~z3model.Full, c~Context, u~Unknown, r~(Bytes, Bytes)
    let sig = term.signature c
    let unread = b"Z3 printed it, but this reader couldn't evaluate it"
    match u
        NotGiven (Fun f)       ->
            if z3model.printed_fun sig full f
                (unread, b"Z3 printed `" ++ name_of sig f ++ b"`, but this reader can't evaluate what it printed")
            else
                (b"a function Z3's model leaves out", reason c u False)
        NotGiven (Prim Div)    ->
            if z3model.printed_name full b"div0" then (unread, b"div0") else (b"a division by zero Z3's model leaves out", b"div0")
        NotGiven (Prim Mod)    ->
            if z3model.printed_name full b"mod0" then (unread, b"mod0") else (b"a remainder by zero Z3's model leaves out", b"mod0")
        NotGiven (Prim SeqNth) ->
            if z3model.printed_name full b"seq.nth_u"
                (unread, b"seq.nth_u")
            else
                (b"`seq.nth` out of range, which Z3's model leaves out", b"seq.nth_u")
        NotGiven (Prim Select) -> (unread, b"an array of the model")
        NotGiven (Sel _ _ _)   ->
            (b"a selector of another constructor's value: `get-model` doesn't print these", reason c u False)
        _                      -> (reason c u True, reason c u False)

# Ask `z3` (`z3 -in`, as `main compare` runs it) the query `src` with
# `(get-model)` after it, and check the query's assertions in that model.
fn ask t z3 p src -> o : t~Bool, z3~String, p~Proc, src~Bytes, o~Outcome
    match smtlib.parse src
        Err e -> QueryUnread (smtlib.describe src e)
        Ok q  ->
            match proc.run z3 ["-in"] (src ++ b"(get-model)\n") p
                Err e   -> NotRun (string.bytes z3 ++ b": " ++ string.bytes (files.describe e))
                Ok said ->
                    let out = if q.core then answer.without_core_error said.stdout src else said.stdout
                    match answer.verdict out
                        Sat ->
                            match smtlib.read out
                                Err e -> ModelUnread (smtlib.describe out e)
                                Ok es ->
                                    if z3model.bang q.context
                                        BangUnread
                                    else
                                        match smtlib.read src
                                            Err e  -> QueryUnread (smtlib.describe src e)
                                            Ok qes ->
                                                match whole_model t q qes es
                                                    Err w    -> ModelUnread w
                                                    Ok whole ->
                                                        let make = \c -> z3model.model_of c whole FUEL
                                                        check_with t q make (z3model.own_values q.context whole) (\c u -> z3_reason whole c u)
                        v   -> NowAnswers (verdict_text v)

# ── The corpus ───────────────────────────────────────────────────────────────

# Whether `name` ends with `suffix`.
fn ends_with name suffix -> r : name~String, suffix~Bytes, r~Bool
    let b = string.bytes name
    len b > len suffix and bytes.matches_at b (len b - len suffix) suffix

# `name` without its last `k` bytes.
fn stem name k -> r : name~String, k~Nat, r~String
    let b = string.bytes name
    match string.from_utf8 (if len b >= k then bytes.slice b 0 (len b - k) else b)
        Some s -> s
        None   -> name

# Every file in `dirs`, accounted for: each query with its answer (checked
# if Z3 answered `sat`), and anything else listed; `None` if a directory or
# file can't be read.
fn in_dirs how dirs io fs -> r : how~(Bytes -> Bytes -> Outcome), dirs~List String, io~Term, fs~Fs, r~Option (List (Bytes, Outcome))
    match dirs
        []          -> Some []
        dir :: rest ->
            match files.list dir fs
                Err e ->
                    let _ = terminal.eprint_line ("error: " ++ dir ++ ": " ++ files.describe e) io
                    None
                Ok es ->
                    let names = list.map (\e -> e.name) es
                    match (each how dir names es io fs, in_dirs how rest io fs)
                        (Some xs, Some ys) -> Some (xs ++ ys)
                        _                  -> None

fn each how dir names es io fs -> r : how~(Bytes -> Bytes -> Outcome), dir~String, names~List String, es~List Entry, io~Term,
                                      fs~Fs, r~Option (List (Bytes, Outcome))
    match es
        []        -> Some []
        e :: rest ->
            let base = \k -> (if ends_with dir b"/" then dir else dir ++ "/") ++ stem e.name k
            let here =
                if e.dir
                    Some (Some (string.bytes (dir ++ "/" ++ e.name), Stray b"a directory"))
                else if ends_with e.name b".z3"
                    if list.contains names (stem e.name 3 ++ ".smt2")
                        match pair how (base 3) io fs
                            Some o -> Some (Some (string.bytes (base 3), o))
                            None   -> None
                    else
                        Some (Some (string.bytes (base 3), QueryUnread b"no such file, beside its answer"))
                else if ends_with e.name b".smt2"
                    if list.contains names (stem e.name 5 ++ ".z3") then Some None else Some (Some (string.bytes (base 5), AnswerUnread b"no such file, beside its query"))
                else
                    Some (Some (string.bytes (dir ++ "/" ++ e.name), Stray b"neither a query (`.smt2`) nor an answer (`.z3`)"))
            match (here, each how dir names rest io fs)
                (Some (Some x), Some more) -> Some (x :: more)
                (Some None, Some more)     -> Some more
                _                          -> None

# The query `base.smt2` and its answer `base.z3`: checked if Z3 answered
# `sat`.
fn pair how base io fs -> r : how~(Bytes -> Bytes -> Outcome), base~String, io~Term, fs~Fs, r~Option Outcome
    let z3_path = base ++ ".z3"
    let query_path = base ++ ".smt2"
    match (files.read z3_path fs, files.read query_path fs)
        (Err err, _)    ->
            let _ = terminal.eprint_line ("error: " ++ z3_path ++ ": " ++ files.describe err) io
            None
        (_, Err err)    ->
            let _ = terminal.eprint_line ("error: " ++ query_path ++ ": " ++ files.describe err) io
            None
        (Ok z3, Ok src) ->
            match answer.verdict z3
                Sat    -> Some (how src z3)
                Unsat  -> Some (Answered b"unsat")
                GaveUp -> Some (Answered b"unknown")
                Other  -> Some (AnswerUnread b"its first line after the comments is not exactly `sat`, `unsat` or `unknown`")

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
                    ModelUnread w  -> p ++ b": Z3's model doesn't read: " ++ w ++ b"\n"
                    NowAnswers w   -> p ++ b": Z3 now answers " ++ w ++ b"\n"
                    NotRun w       -> p ++ b": can't run " ++ w ++ b"\n"
                    Fails w        -> p ++ b": Z3's model is not a model: " ++ w ++ b"\n"
                    Disagrees      -> p ++ b": `refutes` disagrees with the assertions one by one\n"
                    Stray w        -> p ++ b": " ++ w ++ b"\n"
                    BangUnread     -> p ++ b": not read: " ++ z3model.BANG ++ b"\n"
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

fn is_answered v o -> r : v~Bytes, o~Outcome, r~Bool
    match o
        Answered w -> w == v
        _          -> False

fn is_stray o -> r : o~Outcome, r~Bool
    match o
        Stray _ -> True
        _       -> False

fn is_bang o -> r : o~Outcome, r~Bool
    match o
        BangUnread -> True
        _          -> False

fn is_unread o -> r : o~Outcome, r~Bool
    match o
        QueryUnread _  -> True
        AnswerUnread _ -> True
        ModelUnread _  -> True
        _              -> False

fn is_now_answers o -> r : o~Outcome, r~Bool
    match o
        NowAnswers _ -> True
        NotRun _     -> True
        _            -> False

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
        Holds _ _ -> True
        _         -> False

fn is_holds_defs o -> r : o~Outcome, r~Bool
    match o
        Holds True _ -> True
        _            -> False

fn is_holds_lambda o -> r : o~Outcome, r~Bool
    match o
        Holds _ True -> True
        _            -> False

fn is_open o -> r : o~Outcome, r~Bool
    match o
        Undetermined _ _ -> True
        _                -> False

fn is_disagrees o -> r : o~Outcome, r~Bool
    match o
        Disagrees -> True
        _         -> False

# What the output says of definitions.
fn terms_line terminating -> r : terminating~Bool, r~Bytes
    if terminating
        b"definitions: each taken as terminating, on the word of whoever ran this (`--terminating`)\n"
    else
        b"definitions: none taken as terminating (`--terminating` takes each so)\n"

fn defs_how terminating -> r : terminating~Bool, r~Bytes
    if terminating then b"taken as terminating" else b"none called"

# The report on `xs`: the queries listed, then the counts.
export fn report terminating xs -> r : terminating~Bool, xs~List (Bytes, Outcome), r~Bytes
    let n = \p -> count p xs
    listed xs ++ terms_line terminating ++ smtlib.numeral (list.length xs) ++ b" queries and other files\n"
        ++ line (n is_stray) b"neither a query nor an answer (listed above)"
        ++ line (n (is_answered b"unsat")) b"answered `unsat`: no model to check (nothing after `unsat` is read)"
        ++ line (n (is_answered b"unknown")) b"answered `unknown`: no model to check (nothing after `unknown` is read)"
        ++ line (n is_now_answers) b"where Z3 run now doesn't answer `sat`, or can't be run (with `--z3`; listed above, and fail the run)"
        ++ line (n is_no_values) b"without `(get-value …)`: no values printed (nothing after `sat` is read)"
        ++ line (n is_bang) b"with a name with `!`, as Z3's own names: not read, and fail the run (listed above)"
        ++ line (n is_unread) b"whose query, answer or model doesn't read (listed above)"
        ++ line (n is_unpatterned) b"with a `forall` without `:pattern`: not checked"
        ++ line (n is_patterned) b"with only `forall`s with `:pattern`: not checked"
        ++ line (n is_fails) b"with an assertion false in Z3's model (listed above)"
        ++ line (n is_holds) b"where every assertion holds"
        ++ b"      (" ++ smtlib.numeral (n is_holds_defs) ++ b" of them with definitions, " ++ defs_how terminating ++ b")\n"
        ++ b"      (" ++ smtlib.numeral (n is_holds_lambda) ++ b" of them with a `lambda`, which `refutes` refuses)\n"
        ++ line (n is_open) b"not determined by what Z3 printed, by the first reason:"
        ++ reason_lines (reasons xs [])
        ++ line (n is_disagrees) b"where `refutes` disagrees (listed above)"

# `main models [--terminating] [--z3 PROGRAM] DIR…`: with `--z3`, the
# models are asked of PROGRAM run now; without, they are the values
# recorded in the corpus. With `--terminating`, every definition is taken
# as terminating.
export fn run args io fs p -> ok : args~List String, io~Term, fs~Fs, p~Proc, ok~Bool
    let (t, rest) =
        match args
            "--terminating" :: more -> (True, more)
            _                       -> (False, args)
    let how =
        match rest
            "--z3" :: prog :: _ -> \src _ -> ask t prog p src
            _                   -> \src z3 -> check_query t src z3
    let dirs =
        match rest
            "--z3" :: _ :: more -> more
            _                   -> rest
    if dirs == []
        let _ = terminal.eprint_line "error: `models` takes at least one directory: main models [--terminating] [--z3 PROGRAM] DIR…" io
        False
    else
        match in_dirs how dirs io fs
            None    -> False
            Some xs ->
                let _ = terminal.write_bytes (report t xs) io
                count is_unread xs == 0 and count is_stray xs == 0 and count is_fails xs == 0 and count is_disagrees xs == 0
                    and count is_now_answers xs == 0 and count is_bang xs == 0

# ── One query ────────────────────────────────────────────────────────────────

fn came_text c k why -> r : c~Context, k~Came, why~(Context -> Unknown -> Bytes), r~Bytes
    match k
        Right  -> b"holds"
        Wrong  -> b"fails"
        Open u -> b"not determined: " ++ why c u

fn fact_lines c rs why -> r : c~Context, rs~List (Nat, Came), why~(Context -> Unknown -> Bytes), r~Bytes
    match rs
        []             -> b""
        (n, k) :: rest -> b"fact " ++ smtlib.numeral n ++ b": " ++ came_text c k why ++ b"\n" ++ fact_lines c rest why

# `main model [--terminating] QUERY ANSWER`: each assertion of the query in the model of
# the answer (the model that knows nothing, if Z3 printed no values).
export fn one src z3 terminating -> r : src~Bytes, z3~Bytes, terminating~Bool, r~Bytes
    let head = b"z3: " ++ verdict_text (answer.verdict z3) ++ b"\n"
    match smtlib.parse src
        Err e -> head ++ b"the query doesn't read: " ++ smtlib.describe src e ++ b"\n"
        Ok q  ->
            match model_maker terminating q src z3
                Err why                           -> head ++ why ++ b"\n"
                Ok (kind, make, printed_own, why) ->
                    match (if terminating then marked q.context else Ok q.context)
                        Err why -> head ++ why ++ b"\n"
                        Ok c    ->
                            let m = make c
                            let goal = came (model.eval_unfolding c m q.goal) False
                            let axioms = term.axioms c
                            let note = if axioms == [] then b"" else b"a `forall`: not evaluated\n"
                            let defs = if has_recursive (term.defs c) then terms_line terminating else b""
                            let last =
                                if answer.verdict z3 != Sat
                                    b""
                                else if first_other c m printed_own != None
                                    b"no model: a value Z3 printed isn't what the query gives its term\n"
                                else
                                    b"refutes: " ++ refutes_text c q.goal m ++ b"\n"
                            head ++ kind ++ defs ++ note ++ own_lines c m printed_own why ++ fact_lines c (each_fact c m (term.facts c) 1) why
                                ++ b"the negated goal: " ++ came_text c goal why ++ b"\n" ++ last

# For each constant the query defines and each named assertion, whose
# value Z3 printed, whether it is what the query gives its term.
fn own_lines c m printed_own why -> r : c~Context, m~model.Model, printed_own~List (Name, term.Term, Option Value), why~(Context -> Unknown -> Bytes),
                                        r~Bytes
    match printed_own
        []                 -> b""
        (n, t, ov) :: rest ->
            let said =
                match ov
                    None   -> b"printed, but this reader can't evaluate what it printed"
                    Some v ->
                        match model.eval_unfolding c m t
                            Ok w  -> if w == v then b"as the query gives it" else b"not what the query gives it"
                            Err u -> b"not determined: " ++ why c u
            b"Z3's value of `" ++ n ++ b"`: " ++ said ++ b"\n" ++ own_lines c m rest why

# The `f`-th function's name.
fn name_of sig f -> r : sig~term.Sig, f~Nat, r~Bytes
    if f < len sig.funs then sig.funs[f].name else b"?"

# Whether any of `ds` is recursive: only those take a termination mark.
fn has_recursive ds -> r : ds~List (Nat, term.Def), r~Bool
    match ds
        []             -> False
        (_, d) :: rest ->
            match d.kind
                Recursive -> True
                Plain     -> has_recursive rest

# Whether `refutes` takes `m`, and if it doesn't for a reason other than an
# assertion, which.
fn refutes_text c goal m -> r : c~Context, goal~term.Term, m~model.Model, r~Bytes
    if model.refutes c goal m
        b"yes"
    else if term.axioms c != []
        b"no (a `forall`)"
    else if not (model.without_lambda c goal)
        b"no (a `lambda`)"
    else if not (model.defs_run c)
        b"no (recursive definitions not taken as terminating)"
    else
        b"no"

# The items of `e`, if it is what `(get-model)` prints: a list of
# `define-fun`s, `declare-fun`s and cardinality constraints, empty for an
# empty model.
fn model_list e -> r : e~SExpr src, r~Option (List (SExpr src))
    match e
        Node items _ -> if list.all model_item items then Some items else None
        _            -> None

fn model_item e -> r : e~SExpr src, r~Bool
    match e
        Node (Leaf (Symbol k False) _ :: _) _ -> k == b"define-fun" or k == b"declare-fun" or k == b"forall"
        _                                     -> False

let UNREAD = b"the answer doesn't read: "

let AFTER_SAT = b"after `sat`, not exactly what the query asks for: its `(get-value …)` list, if it has one, then the model"

let NOT_GIVEN_BY = b"a value printed for `(get-value …)` isn't what the model printed gives its term"

# What an answer to `q` with `(get-model)` after it holds after `sat`: the
# `(get-value …)` list if `q` asks one, and the model's items; `None` if
# it holds anything else.
fn model_items q es -> r : q~Query, es~List (SExpr src), r~Option (Option (SExpr src), List (SExpr src))
    match (q.values, es)
        (None, [Leaf (Symbol v False) _, m])         ->
            if v == b"sat"
                match model_list m
                    Some items -> Some (None, items)
                    None       -> None
            else
                None
        (Some _, [Leaf (Symbol v False) _, vals, m]) ->
            if v == b"sat"
                match model_list m
                    Some items -> Some (Some vals, items)
                    None       -> None
            else
                None
        _                                            -> None

# The model `(get-model)` printed in the answer `es` to `q` (whose
# S-expressions are `qes`), read whole; and the `(get-value …)` list before
# it, if `q` asks one, read too, with the model's universes: each value
# must be what that model gives its term, wherever the model determines
# it, the query's definitions run as their bodies (marked terminating if
# `t`).
fn whole_model t q qes es -> r : t~Bool, q~Query, qes~List (SExpr qsrc), es~List (SExpr src), r~Result z3model.Full Bytes
    match model_items q es
        None               -> Err AFTER_SAT
        Some (vals, items) ->
            let whole = try z3model.full q.context items
            match (q.values, vals)
                (Some ts, Some v) ->
                    let c = try context_for t q
                    let ps = try answer.values_list c ts (answer.asked qes) v whole.universes False
                    if answer.given_by c ps (z3model.model_of c whole FUEL) then Ok whole else Err NOT_GIVEN_BY
                _                 -> Ok whole

# The model an answer gives, a line saying which kind it is, and why a
# term isn't determined in it: what `(get-model)` printed, if the answer
# ends with that; else the `(get-value …)` values; else, after `sat` with
# nothing asked, the model that knows nothing. After `unsat` or `unknown`
# there is no model: the assertions are evaluated with nothing given (a
# closed term still has its value), and `refutes` isn't asked.
fn model_maker t q src z3 -> r : t~Bool, q~Query, src~Bytes, z3~Bytes,
                                 r~Result (Bytes, (Context -> model.Model), List (Name, term.Term, Option Value), (Context -> Unknown -> Bytes)) Bytes
    let plain = \c u -> reason c u False
    let v = answer.verdict z3
    if v != Sat
        let kind = b"no model: Z3 answered " ++ verdict_text v ++ b"; the assertions with nothing given:\n"
        Ok (kind, \c -> answer.empty_model (term.signature c) FUEL, [], plain)
    else if z3model.bang q.context
        Err (b"no model read: " ++ z3model.BANG)
    else
        let text = if q.core then answer.without_core_error z3 src else z3
        match (smtlib.read text, smtlib.read src)
            (Err e, _)      -> Err (UNREAD ++ smtlib.describe text e)
            (_, Err e)      -> Err (b"the query doesn't read: " ++ smtlib.describe src e)
            (Ok es, Ok qes) ->
                match (model_items q es, q.values, es)
                    (Some _, _, _)                          ->
                        match whole_model t q qes es
                            Err why  -> Err (UNREAD ++ why)
                            Ok whole ->
                                let why = \c u ->
                                    let (_, detail) = z3_reason whole c u
                                    detail
                                Ok (b"model: (get-model)\n", \c -> z3model.model_of c whole FUEL, z3model.own_values q.context whole, why)
                    (None, Some ts, _)                      ->
                        let c = try context_for t q
                        match answer.printed c ts (answer.asked qes) es
                            Err why -> Err (UNREAD ++ why)
                            Ok ps   -> Ok (b"model: (get-value …)\n", \c -> answer.model_of c [] ps FUEL, [], \c u -> values_reason c ts ps u False)
                    (None, None, [Leaf (Symbol w False) _]) ->
                        if w == b"sat" then Ok (b"", \c -> answer.empty_model (term.signature c) FUEL, [], plain) else Err (UNREAD ++ AFTER_SAT)
                    _                                       -> Err (UNREAD ++ AFTER_SAT)

fn verdict_text v -> r : v~Verdict, r~Bytes
    match v
        Sat    -> b"sat"
        Unsat  -> b"unsat"
        GaveUp -> b"unknown"
        Other  -> b"no answer"
