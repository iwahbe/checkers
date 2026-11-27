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
import term (Term, Context, Var, App, Let, Lam, ConstOf)
import model (Model)
import cert (Refutation, Step, Fact, NotGoal, Structure, Resolve, Lit)

# How much work `solve` may do, in its own units (#72, design 5): here, one
# unit per clause looked at.
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
    let inputs = clauses c goal
    let numbered = number 0 inputs
    let made = list.length inputs
    if made >= lim.work
        Outcome (Unknown OutOfWork None) lim.work
    else
        match sweep numbered numbered [] False (lim.work - made)
            Found conflict assigned used ->
                let refutation = refutation_of numbered (reasons (list.reverse assigned) ++ [conflict])
                let work = made + used
                if cert.checks c goal refutation
                    Outcome (Valid refutation) (if work <= lim.work then work else lim.work)
                else
                    # Propagation found a conflict the checker doesn't
                    # accept: a bug in the search, never an answer.
                    Outcome (Unknown (Unsupported "a refutation `cert.checks` rejects") None) (if work <= lim.work then work else lim.work)
            Fixpoint used                ->
                let work = made + used
                Outcome (Unknown Incomplete None) (if work <= lim.work then work else lim.work)
            Exhausted                    -> Outcome (Unknown OutOfWork None) lim.work

# ── The clauses ──────────────────────────────────────────────────────────────

# A clause the search may use, and the step that adds it.
record Input
    lits~List Lit
    step~Step

# The facts, the goal taken as false, and the clauses of the Boolean
# structure of every connective reachable from them.
fn clauses c goal -> r : c~Context, goal~Term, r~List Input
    let facts = term.facts c
    let units = fact_units c facts 0 ++ (if model.boolean c goal then [Input [Lit False goal] NotGoal] else [])
    let roots = goal :: facts
    units ++ expand c roots [] (term_count roots)

fn fact_units c fs k -> r : c~Context, fs~List Term, k~Nat, r~List Input
    match fs
        []        -> []
        f :: rest ->
            let more = fact_units c rest (k + 1)
            if model.boolean c f then Input [Lit True f] (Fact k) :: more else more

# How many terms `ts` has in them, counting each subterm: enough to visit
# each once.
fn term_count ts -> n : ts~List Term, n~Nat
    match ts
        []        -> 0
        t :: rest -> size t + term_count rest

fn binds_count bs -> n : bs~List (term.Name, Term), n~Nat
    match bs
        []             -> 0
        (_, t) :: rest -> size t + binds_count rest

fn size t -> n : t~Term, n~Nat
    match t
        Var _          -> 1
        App _ args     -> 1 + term_count args
        Let binds body -> 1 + binds_count binds + size body
        Lam _ _ body   -> 1 + size body

# The structure clauses of each connective reachable from `todo` through
# parts, skipping those in `seen`. `budget` bounds the terms visited.
fn expand c todo seen budget -> r : c~Context, todo~List Term, seen~List Term, budget~Nat, r~List Input
    decreasing budget
    if budget == 0
        []
    else
        match todo
            []        -> []
            t :: rest ->
                if list.contains seen t
                    expand c rest seen (budget - 1)
                else
                    let ps = cert.parts (term.structure t)
                    if ps != [] and model.boolean c t and model.booleans c ps
                        structure_of t 0 (list.length ps + 4) ++ expand c (ps ++ rest) (t :: seen) (budget - 1)
                    else if model.boolean c t and is_constant t
                        structure_of t 0 1 ++ expand c rest (t :: seen) (budget - 1)
                    else
                        expand c rest (t :: seen) (budget - 1)

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
    Exhausted

# Look at each of `todo`, then at all of `all` again if anything was
# assigned, until a conflict or nothing changes.
fn sweep todo all assigned changed budget -> r : todo~List (Nat, Input), all~List (Nat, Input), assigned~List Assigned,
                                                 changed~Bool, budget~Nat, r~Swept
    decreasing budget
    if budget == 0
        Exhausted
    else
        match todo
            []              -> if changed then counted (sweep all all assigned False (budget - 1)) else Fixpoint 1
            (id, i) :: rest ->
                match status assigned i.lits None
                    Conflict -> Found id assigned 1
                    Unit l   -> counted (sweep rest all (Assigned l.atom l.pos id :: assigned) True (budget - 1))
                    _        -> counted (sweep rest all assigned changed (budget - 1))

# One more clause looked at.
fn counted r -> s : r~Swept, s~Swept
    match r
        Found k a used -> Found k a (used + 1)
        Fixpoint used  -> Fixpoint (used + 1)
        Exhausted      -> Exhausted

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
