# solve.ck — the solver's top level (#72, "Interface").
#
# `solve` answers whether a goal follows from a context. Its answers are
# never trusted: `Valid` carries a refutation that `cert.checks` accepted
# (so `cert.checks_sound` applies to it), `Invalid` a model that
# `model.refutes` accepted, and anything else is `Unknown`, with why.
#
# The search here is unit propagation only (#86, S6a): over the facts, the
# goal taken as false, and the clauses the Boolean structure of their terms
# gives (`cert.structure_clause`). It finds a refutation when propagation
# alone reaches a clause with every literal false, and otherwise gives up
# (`Incomplete`). It never answers `Invalid`: a model needs the theories
# (S6e). The search is not proved; its answers are checked.

module solve

import std.list
import term (Term, Context, ConstOf)
import model (Model)
import cert (Refutation, Step, Fact, NotGoal, Structure, Resolve, Lit)

# How much work `solve` may do, in its own units (#72, design 5): here, one
# unit per term looked at, per clause made, and per clause looked at in
# propagation.
export record Limits
    work~Nat

# Why `solve` gave up.
export enum GiveUp
    # It used all the work it was allowed.
    OutOfWork
    # The query needs something it doesn't do, named by `what`.
    Unsupported what : what~String
    # It tried everything it knows and found no answer.
    Incomplete

# The work shared by every goal under `c`. Persistent: extending it with
# `assume` leaves it usable.
export abstract record Prepared c : c~ghost Context
    context~Context, context == c

export fn prepare c -> p : c~Context, p~Prepared c
    Prepared c

# #72's `assume` (`p` with facts added, `q~Prepared (term.with_facts c fs)`)
# waits for #488: a call in a result type can't yet use the preconditions
# before it.

# The answer about `goal` under `c`.
export enum Answer c goal : c~ghost Context, goal~ghost Term
    # `goal` follows: `refutation` refutes the facts and `not goal`.
    Valid refutation  : refutation~Refutation, cert.checks c goal refutation
    # `m` is a counterexample: the facts hold in it, and `goal` fails.
    Invalid m         : m~Model, model.refutes c goal m
    Unknown why guess : why~GiveUp, guess~Option Model

# What an answer says, without its evidence: for modules that also name
# answers of their own.
export enum Verdict
    Proved
    Refuted
    GaveUp why : why~GiveUp

export fn verdict a -> v : a~Answer c goal, v~Verdict
    match a
        Valid _       -> Proved
        Invalid _     -> Refuted
        Unknown why _ -> GaveUp why

export record Outcome c goal lim : c~ghost Context, goal~ghost Term, lim~ghost Limits
    answer~Answer c goal
    work~Nat, work <= lim.work

# A pure function of its arguments: the same answer whatever else was solved.
export fn solve p goal lim -> r : p~Prepared c, goal~Term, lim~Limits, r~Outcome c goal lim
    let c = p.context
    let made = gather c goal lim.work
    # What making the clauses used.
    let spent = lim.work - made.left
    if not made.done
        Outcome (Unknown OutOfWork None) spent
    else
        let numbered = number 0 made.inputs
        let swept = sweep numbered numbered [] False made.left
        let work = spent + used swept
        match swept
            Found conflict assigned _ ->
                let refutation = refutation_of numbered (reasons (list.reverse assigned) ++ [conflict])
                if cert.checks c goal refutation
                    Outcome (Valid refutation) work
                else
                    # The checker refused what propagation found: the goal
                    # isn't a closed `Bool` term of `c` (never so for a
                    # query's, `smtlib.query_goal_boolean`), or the search
                    # has a bug. Never an answer.
                    Outcome (Unknown (Unsupported "a refutation `cert.checks` rejects") None) work
            Fixpoint _                -> Outcome (Unknown Incomplete None) work
            Exhausted _               -> Outcome (Unknown OutOfWork None) work

# ── The clauses ──────────────────────────────────────────────────────────────

# A clause the search may use, and the step that adds it.
record Input
    lits~List Lit
    step~Step

# Clauses made, and the work left after making them: one unit for each
# term looked at and each clause made. `done` is false if the work ran out
# first; then `inputs` is what was made before it did.
record Made
    inputs~List Input
    left~Nat
    done~Bool

# The facts, the goal taken as false, and the clauses of the Boolean
# structure of every connective reachable from them, within `budget`.
fn gather c goal budget -> r : c~Context, goal~Term, budget~Nat, r~Made, r.left <= budget
    let facts = term.facts c
    let units = fact_units c facts 0 budget
    if not units.done
        units
    else if units.left == 0
        Made units.inputs 0 False
    else
        let g = if model.boolean c goal then [Input [Lit False goal] NotGoal] else []
        let more = expand c (goal :: facts) [] (units.left - 1)
        Made (units.inputs ++ g ++ more.inputs) more.left more.done

fn fact_units c fs k budget -> r : c~Context, fs~List Term, k~Nat, budget~Nat, r~Made, r.left <= budget
    match fs
        []        -> Made [] budget True
        f :: rest ->
            if budget == 0
                Made [] 0 False
            else
                let more = fact_units c rest (k + 1) (budget - 1)
                let here = if model.boolean c f then [Input [Lit True f] (Fact k)] else []
                Made (here ++ more.inputs) more.left more.done

# The structure clauses of each connective reachable from `todo` through
# parts, skipping those in `seen`, within `budget`.
fn expand c todo seen budget -> r : c~Context, todo~List Term, seen~List Term, budget~Nat, r~Made, r.left <= budget
    decreasing budget
    match todo
        []        -> Made [] budget True
        t :: rest ->
            if budget == 0
                Made [] 0 False
            else if list.contains seen t
                expand c rest seen (budget - 1)
            else
                let ps = cert.parts (term.structure t)
                let made = if ps != [] and model.boolean c t and model.booleans c ps
                    structure_of t 0 (list.length ps + 4)
                else if model.boolean c t and is_constant t
                    structure_of t 0 1
                else
                    []
                let cost = 1 + list.length made
                if cost > budget
                    Made [] budget False
                else
                    let more = expand c (ps ++ rest) (t :: seen) (budget - cost)
                    Made (made ++ more.inputs) more.left more.done

fn is_constant t -> r : t~Term, r~Bool
    match term.structure t
        ConstOf _ -> True
        _         -> False

# Clauses `which`, `which + 1`, … of `t`'s structure, at most `count`.
fn structure_of t which count -> r : t~Term, which~Nat, count~Nat, r~List Input
    if count == 0
        []
    else
        match cert.structure_clause t which
            Some cl -> Input cl (Structure t which) :: structure_of t (which + 1) (count - 1)
            None    -> []

fn number k inputs -> r : k~Nat, inputs~List Input, r~List (Nat, Input)
    match inputs
        []        -> []
        i :: rest -> (k, i) :: number (k + 1) rest

# ── Unit propagation ─────────────────────────────────────────────────────────

# An atom given a value, and the clause that gave it.
record Assigned
    atom~Term
    value~Bool
    reason~Nat

# What a clause is, under what is assigned.
enum Status
    Satisfied
    Conflict
    Unit l : l~Lit
    Open

fn value_of assigned t -> r : assigned~List Assigned, t~Term, r~Option Bool
    match assigned
        []        -> None
        a :: rest -> if a.atom == t then Some a.value else value_of rest t

fn status assigned lits found -> r : assigned~List Assigned, lits~List Lit, found~Option Lit, r~Status
    match lits
        []        ->
            match found
                Some l -> Unit l
                None   -> Conflict
        l :: rest ->
            match value_of assigned l.atom
                Some b -> if b == l.pos then Satisfied else status assigned rest found
                None   ->
                    match found
                        Some _ -> more_open assigned rest
                        None   -> status assigned rest (Some l)

# Two literals are open: satisfied if another is true, else open.
fn more_open assigned lits -> r : assigned~List Assigned, lits~List Lit, r~Status
    match lits
        []        -> Open
        l :: rest ->
            match value_of assigned l.atom
                Some b -> if b == l.pos then Satisfied else more_open assigned rest
                None   -> more_open assigned rest

# How propagation ended: a clause `conflict` with every literal false (with
# the atoms assigned, the last first), no clause left to propagate, or out
# of work. `used` counts the clauses looked at.
enum Swept
    Found conflict assigned used : conflict~Nat, assigned~List Assigned, used~Nat
    Fixpoint used                : used~Nat
    Exhausted used               : used~Nat

fn used r -> n : r~Swept, n~Nat
    match r
        Found _ _ n -> n
        Fixpoint n  -> n
        Exhausted n -> n

# Look at each of `todo`, then at all of `all` again if anything was
# assigned, until a conflict or nothing changes.
fn sweep todo all assigned changed budget -> r : todo~List (Nat, Input), all~List (Nat, Input), assigned~List Assigned,
                                                 changed~Bool, budget~Nat, r~Swept, used r <= budget
    decreasing budget
    if budget == 0
        Exhausted 0
    else
        match todo
            []              -> if changed then counted (sweep all all assigned False (budget - 1)) else Fixpoint 1
            (id, i) :: rest ->
                match status assigned i.lits None
                    Conflict -> Found id assigned 1
                    Unit l   -> counted (sweep rest all (Assigned l.atom l.pos id :: assigned) True (budget - 1))
                    _        -> counted (sweep rest all assigned changed (budget - 1))

# One more clause looked at.
fn counted r -> s : r~Swept, s~Swept, used s == used r + 1
    match r
        Found k a n -> Found k a (n + 1)
        Fixpoint n  -> Fixpoint (n + 1)
        Exhausted n -> Exhausted (n + 1)

fn reasons assigned -> r : assigned~List Assigned, r~List Nat
    match assigned
        []        -> []
        a :: rest -> a.reason :: reasons rest

# ── The refutation ───────────────────────────────────────────────────────────

# The steps of the clauses `hints` names, renumbered in order, then the
# empty clause by unit propagation along them.
fn refutation_of numbered hints -> r : numbered~List (Nat, Input), hints~List Nat, r~Refutation
    let used = used_inputs numbered hints
    let ids = list.map (\(id, _) -> id) used
    Refutation (list.map (\(_, i) -> i.step) used ++ [Resolve [] (renumber ids hints)])

fn used_inputs numbered hints -> r : numbered~List (Nat, Input), hints~List Nat, r~List (Nat, Input)
    match numbered
        []              -> []
        (id, i) :: rest -> if list.contains hints id then (id, i) :: used_inputs rest hints else used_inputs rest hints

fn renumber ids hints -> r : ids~List Nat, hints~List Nat, r~List Nat
    match hints
        []        -> []
        h :: rest -> position ids h 0 :: renumber ids rest

fn position ids h k -> r : ids~List Nat, h~Nat, k~Nat, r~Nat
    match ids
        []        -> k
        i :: rest -> if i == h then k else position rest h (k + 1)
