# cert.ck — refutations, the checker `checks`, and why it is sound.
#
# A `Valid` answer carries a `Refutation`: steps that each add a clause,
# numbered from 0 in order, the last of them the empty clause. The clauses
# are made of literals, closed `Bool` terms of the context taken as true or
# false. A step adds a fact of the context, the goal taken as false, a
# clause the Boolean structure of a term gives (`term.structure`), or a
# clause that unit propagation on clauses before it shows to follow (in
# the style of LRAT: the step names the clauses, in the order propagation
# uses them). `checks` checks every step.
#
# `checks_sound` is the theorem the solver rests on (#72, design 1; the
# statement decided on #84 and #86): if `checks` accepts a refutation, the
# goal is true in every model of the context's facts in which the terms the
# refutation uses have values and the context's axioms, definitions and
# array laws hold at their values. Every satisfiable context has such a
# model, so it says something about every query.
#
# **Later steps.** A theory's step (congruence, arithmetic, datatypes,
# arrays, an axiom's instance) is one more `Step` constructor adding one
# clause: `checks` checks it, its atoms are among the terms it uses, and
# its soundness rests on premises `checks_sound` already has (values of the
# terms used; axioms, definitions and array laws at their values). So
# adding one changes `checks` and the proof, not the statement.

module cert

import std.list
import term (Term, Context, Axiom, Def, Sort)
import term (Connective, ConstOf, NotOf, AndOf, OrOf, ImpliesOf, IteOf, IffOf)
import model (Model, Value, ArrayElem)

# ── Refutations ──────────────────────────────────────────────────────────────

# A literal: `atom` taken as true (`pos`) or as false.
export record Lit
    pos~Bool
    atom~Term

# One step of a refutation; each adds one clause.
#
# A known limit of this frame, for the theory steps to come: a step can
# only name terms, and `Term` has no head for the index `model.differ`
# gives two different arrays, so an extensionality step needs one first
# (S6c, S6e).
export enum Step
    # The `k`-th fact of the context (`term.facts`, from 0): `[fact]`.
    Fact k               : k~Nat
    # The goal, false: `[not goal]`.
    NotGoal
    # Clause `which` of those the Boolean structure of `t` gives
    # (`structure_clause`).
    Structure t which    : t~Term, which~Nat
    # `clause`, because unit propagation on the clauses numbered `hints`, in
    # that order, starting from the negation of `clause`, ends in a clause
    # with every literal false.
    Resolve clause hints : clause~List Lit, hints~List Nat

# The steps; the last one adds the empty clause.
export record Refutation
    steps~List Step

# ── The clauses of a step ────────────────────────────────────────────────────

export transparent fn negated l -> r : l~Lit, r~Lit
    Lit (not l.pos) l.atom

export transparent fn atoms cl -> ts : cl~List Lit, ts~List Term
    match cl
        []        -> []
        l :: rest -> l.atom :: atoms rest

fn yes t -> l : t~Term, l~Lit
    Lit True t

fn no t -> l : t~Term, l~Lit
    Lit False t

# Each of `ts`, false.
export transparent fn all_no ts -> r : ts~List Term, r~List Lit
    match ts
        []        -> []
        t :: rest -> Lit False t :: all_no rest

# Each of `ts`, true.
export transparent fn all_yes ts -> r : ts~List Term, r~List Lit
    match ts
        []        -> []
        t :: rest -> Lit True t :: all_yes rest

# The clauses the Boolean structure of `t` gives, numbered by `which`:
#
# | `t` is            | clauses                                                            |
# |-------------------|--------------------------------------------------------------------|
# | `b` (a constant)  | 0: `[t]` if `b`, `[not t]` if not                                   |
# | `(not a)`         | 0: `[not t, not a]`; 1: `[t, a]`                                     |
# | `(and p…)`        | 0: `[t, not p…]`; 1 + i: `[not t, p_i]`                             |
# | `(or p…)`         | 0: `[not t, p…]`; 1 + i: `[t, not p_i]`                             |
# | `(=> a b)`        | 0: `[not t, not a, b]`; 1: `[t, a]`; 2: `[t, not b]`                |
# | `(ite p a b)`     | 0: `[not t, not p, a]`; 1: `[not t, p, b]`; 2: `[t, not p, not a]`; 3: `[t, p, not b]` |
# | `(= a b)`         | 0: `[not t, not a, b]`; 1: `[not t, a, not b]`; 2: `[t, a, b]`; 3: `[t, not a, not b]` |
export transparent fn structure_clause t which -> r : t~Term, which~Nat, r~Option (List Lit)
    match term.structure t
        ConstOf b     -> if which == 0 then Some [Lit b t] else None
        NotOf a       -> if which == 0 then Some [no t, no a] else if which == 1 then Some [yes t, yes a] else None
        AndOf ps      ->
            if which == 0
                Some (yes t :: all_no ps)
            else
                match list.head (list.drop (which - 1) ps)
                    Some p -> Some [no t, yes p]
                    None   -> None
        OrOf ps       ->
            if which == 0
                Some (no t :: all_yes ps)
            else
                match list.head (list.drop (which - 1) ps)
                    Some p -> Some [yes t, no p]
                    None   -> None
        ImpliesOf a b ->
            if which == 0
                Some [no t, no a, yes b]
            else if which == 1
                Some [yes t, yes a]
            else if which == 2
                Some [yes t, no b]
            else
                None
        IteOf p a b   ->
            if which == 0
                Some [no t, no p, yes a]
            else if which == 1
                Some [no t, yes p, yes b]
            else if which == 2
                Some [yes t, no p, no a]
            else if which == 3
                Some [yes t, yes p, no b]
            else
                None
        IffOf a b     ->
            if which == 0
                Some [no t, no a, yes b]
            else if which == 1
                Some [no t, yes a, no b]
            else if which == 2
                Some [yes t, yes a, yes b]
            else if which == 3
                Some [yes t, no a, no b]
            else
                None
        _             -> None

# The parts of a connective.
export transparent fn parts s -> ts : s~Connective, ts~List Term
    match s
        NotOf a       -> [a]
        AndOf ps      -> ps
        OrOf ps       -> ps
        ImpliesOf a b -> [a, b]
        IteOf p a b   -> [p, a, b]
        IffOf a b     -> [a, b]
        _             -> []

# The clause step `s` adds, if it names one.
export transparent fn step_clause c goal s -> r : c~Context, goal~Term, s~Step, r~Option (List Lit)
    match s
        Fact k            ->
            match list.head (list.drop k (term.facts c))
                Some f -> Some [yes f]
                None   -> None
        NotGoal           -> Some [no goal]
        Structure t which -> structure_clause t which
        Resolve clause _  -> Some clause

# The terms the steps use: the atoms of the clauses they add.
export transparent fn terms_of c goal steps -> ts : c~Context, goal~Term, steps~List Step, ts~List Term
    match steps
        []        -> []
        s :: rest ->
            match step_clause c goal s
                Some cl -> atoms cl ++ terms_of c goal rest
                None    -> terms_of c goal rest

# The terms `refutation` uses: the goal, and the atoms of the clauses its
# steps add (each fact a `Fact` step cites among them).
export transparent fn terms c goal refutation -> ts : c~Context, goal~Term, refutation~Refutation, ts~List Term
    goal :: terms_of c goal refutation.steps

# ── Checking ─────────────────────────────────────────────────────────────────

# The clauses added so far are `db`, the last first: clause `h` (numbered
# from 0, in the order added) is the one with `h` clauses before it.
export transparent fn clause_at db h -> r : db~List (List Lit), h~Nat, r~Option (List Lit)
    if h < list.length db then list.head (list.drop (list.length db - 1 - h) db) else None

# The literals of `cl` whose negation isn't in `assigned`.
export transparent fn open_lits assigned cl -> r : assigned~List Lit, cl~List Lit, r~List Lit
    match cl
        []        -> []
        l :: rest -> if list.contains assigned (negated l) then open_lits assigned rest else l :: open_lits assigned rest

# Unit propagation along `hints`, from the literals `assigned`: whether it
# reaches a clause with every literal false. Each hint must leave one
# literal open, which is then assigned, or none.
export transparent fn propagate db assigned hints -> r : db~List (List Lit), assigned~List Lit, hints~List Nat, r~Bool
    match hints
        []        -> False
        h :: rest ->
            match clause_at db h
                Some cl ->
                    match open_lits assigned cl
                        []  -> True
                        [l] -> propagate db (l :: assigned) rest
                        _   -> False
                None    -> False

# Each literal of `cl`, negated.
export transparent fn negate_all cl -> r : cl~List Lit, r~List Lit
    match cl
        []        -> []
        l :: rest -> negated l :: negate_all rest

# Whether step `s`, adding `cl` after `db`, is right.
export transparent fn step_ok c db s cl -> r : c~Context, db~List (List Lit), s~Step, cl~List Lit, r~Bool
    match s
        Structure t _   -> model.boolean c t and model.booleans c (parts (term.structure t))
        Resolve _ hints -> propagate db (negate_all cl) hints
        _               -> True

# The clauses after the steps, the last first, if every step is right and
# every atom is a closed `Bool` term of `c`.
export transparent fn run c goal db steps -> r : c~Context, goal~Term, db~List (List Lit), steps~List Step,
                                                 r~Option (List (List Lit))
    match steps
        []        -> Some db
        s :: rest ->
            match step_clause c goal s
                Some cl ->
                    if model.booleans c (atoms cl) and step_ok c db s cl then run c goal (cl :: db) rest else None
                None    -> None

# Whether `refutation` refutes the facts of `c` and the goal taken as false:
# every step is right, and the last adds the empty clause.
export transparent fn checks c goal refutation -> r : c~Context, goal~Term, refutation~Refutation, r~Bool
    match run c goal [] refutation.steps
        Some (last :: _) -> last == []
        _                -> False

# ── Truth of literals and clauses ────────────────────────────────────────────

export transparent fn lit_holds c m l -> r : c~Context, m~Model, l~Lit, r~Bool
    if l.pos then model.holds c m l.atom else model.fails c m l.atom

# Whether some literal of `cl` is true.
export transparent fn clause_holds c m cl -> r : c~Context, m~Model, cl~List Lit, r~Bool
    match cl
        []        -> False
        l :: rest -> lit_holds c m l or clause_holds c m rest

# Whether every literal of `ls` is true.
export transparent fn lits_hold c m ls -> r : c~Context, m~Model, ls~List Lit, r~Bool
    match ls
        []        -> True
        l :: rest -> lit_holds c m l and lits_hold c m rest

# Whether every clause of `db` is true.
export transparent fn db_holds c m db -> r : c~Context, m~Model, db~List (List Lit), r~Bool
    match db
        []         -> True
        cl :: rest -> clause_holds c m cl and db_holds c m rest

# Whether each of `ts` has a value of its sort.
export transparent fn valued c m ts -> r : c~Context, m~Model, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> model.has_value c m t and valued c m rest

lemma lit_not_both c m l : c~Context, m~Model, l~Lit
    ensures not (lit_holds c m l and lit_holds c m (negated l))
    proof
        have model.not_both c m l.atom

lemma lit_two c m l : c~Context, m~Model, l~Lit, model.boolean c l.atom, model.has_value c m l.atom
    ensures lit_holds c m l or lit_holds c m (negated l)
    proof
        have model.two_valued c m l.atom

lemma contains_holds c m ls x : c~Context, m~Model, ls~List Lit, x~Lit, lits_hold c m ls, list.contains ls x
    ensures lit_holds c m x
    proof
        match ls
            []        -> auto
            l :: rest -> if l == x then auto else have contains_holds c m rest x

# A true clause keeps a true literal among those `assigned` doesn't falsify.
lemma open_holds c m assigned cl : c~Context, m~Model, assigned~List Lit, cl~List Lit, lits_hold c m assigned,
                                   clause_holds c m cl
    ensures clause_holds c m (open_lits assigned cl)
    proof
        match cl
            []        -> auto
            l :: rest ->
                if lit_holds c m l
                    if list.contains assigned (negated l)
                        have contains_holds c m assigned (negated l)
                        have lit_not_both c m l
                    else
                        auto
                else
                    have open_holds c m assigned rest

lemma drop_holds c m db k cl : c~Context, m~Model, db~List (List Lit), k~Nat, cl~List Lit, db_holds c m db,
                               list.head (list.drop k db) == Some cl
    ensures clause_holds c m cl
    proof
        match db
            []        -> auto
            d :: rest -> if k == 0 then auto else have drop_holds c m rest (k - 1) cl

lemma at_holds c m db h cl : c~Context, m~Model, db~List (List Lit), h~Nat, cl~List Lit, db_holds c m db,
                             clause_at db h == Some cl
    ensures clause_holds c m cl
    proof
        have drop_holds c m db (list.length db - 1 - h) cl

# From true literals, unit propagation over true clauses never reaches a
# clause with every literal false.
lemma propagate_sound c m db assigned hints : c~Context, m~Model, db~List (List Lit), assigned~List Lit, hints~List Nat,
                                              db_holds c m db, lits_hold c m assigned
    ensures not (propagate db assigned hints)
    proof
        match hints
            []        -> auto
            h :: rest ->
                match clause_at db h
                    Some cl ->
                        have at_holds c m db h cl
                        have open_holds c m assigned cl
                        match open_lits assigned cl
                            []  -> auto
                            [l] -> have propagate_sound c m db (l :: assigned) rest
                            _   -> auto
                    None    -> auto

# A clause that isn't true, whose atoms have values: every literal's
# negation is true.
lemma negations_hold c m cl : c~Context, m~Model, cl~List Lit, model.booleans c (atoms cl), valued c m (atoms cl),
                              not (clause_holds c m cl)
    ensures lits_hold c m (negate_all cl)
    proof
        match cl
            []        -> auto
            l :: rest ->
                have lit_two c m l
                have negations_hold c m rest

lemma resolve_sound c m db cl hints : c~Context, m~Model, db~List (List Lit), cl~List Lit, hints~List Nat,
                                      model.booleans c (atoms cl), valued c m (atoms cl), db_holds c m db,
                                      propagate db (negate_all cl) hints
    ensures clause_holds c m cl
    proof
        if clause_holds c m cl
            auto
        else
            have negations_hold c m cl
            have propagate_sound c m db (negate_all cl) hints

lemma atoms_no ts : ts~List Term
    ensures atoms (all_no ts) == ts
    proof
        match ts
            []        -> auto
            _ :: rest -> have atoms_no rest

lemma atoms_yes ts : ts~List Term
    ensures atoms (all_yes ts) == ts
    proof
        match ts
            []        -> auto
            _ :: rest -> have atoms_yes rest

lemma nth_holds c m ps i p : c~Context, m~Model, ps~List Term, i~Nat, p~Term, model.holds_all c m ps,
                             list.head (list.drop i ps) == Some p
    ensures model.holds c m p
    proof
        match ps
            []        -> auto
            q :: rest ->
                have model.holds_all_cons c m q rest
                if i == 0 then auto else have nth_holds c m rest (i - 1) p

lemma nth_fails c m ps i p : c~Context, m~Model, ps~List Term, i~Nat, p~Term, model.fails_all c m ps,
                             list.head (list.drop i ps) == Some p
    ensures model.fails c m p
    proof
        match ps
            []        -> auto
            _ :: rest -> if i == 0 then auto else have nth_fails c m rest (i - 1) p

lemma nth_fails_one c m ps i p : c~Context, m~Model, ps~List Term, i~Nat, p~Term, model.fails c m p,
                                 list.head (list.drop i ps) == Some p
    ensures model.fails_one c m ps
    proof
        match ps
            []        -> auto
            _ :: rest -> if i == 0 then auto else have nth_fails_one c m rest (i - 1) p

lemma nth_holds_one c m ps i p : c~Context, m~Model, ps~List Term, i~Nat, p~Term, model.holds c m p,
                                 list.head (list.drop i ps) == Some p
    ensures model.holds_one c m ps
    proof
        match ps
            []        -> auto
            _ :: rest -> if i == 0 then auto else have nth_holds_one c m rest (i - 1) p

# Parts with values not all true: one is false.
lemma some_false c m ps : c~Context, m~Model, ps~List Term, model.booleans c ps, valued c m ps,
                          not (model.holds_all c m ps)
    ensures clause_holds c m (all_no ps)
    proof
        match ps
            []        -> have model.holds_all_nil c m
            p :: rest ->
                have model.holds_all_cons c m p rest
                have model.two_valued c m p
                if model.holds c m p then have some_false c m rest else auto

# Parts with values not all false: one is true.
lemma some_true c m ps : c~Context, m~Model, ps~List Term, model.booleans c ps, valued c m ps,
                         not (model.fails_all c m ps)
    ensures clause_holds c m (all_yes ps)
    proof
        match ps
            []        -> auto
            p :: rest ->
                have model.two_valued c m p
                if model.fails c m p then have some_true c m rest else auto

# Whether each of `ts` is true or false.
export transparent fn decided c m ts -> r : c~Context, m~Model, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> (model.holds c m t or model.fails c m t) and decided c m rest

lemma decided_of c m ts : c~Context, m~Model, ts~List Term, model.booleans c ts, valued c m ts
    ensures decided c m ts
    proof
        match ts
            []        -> auto
            t :: rest ->
                have model.two_valued c m t
                have decided_of c m rest

# Every clause the Boolean structure of `t` gives is true, where its atoms
# have values.
lemma structure_sound c m t which cl : c~Context, m~Model, t~Term, which~Nat, cl~List Lit,
                                       structure_clause t which == Some cl, model.boolean c t,
                                       model.booleans c (parts (term.structure t)), model.booleans c (atoms cl),
                                       valued c m (atoms cl)
    ensures clause_holds c m cl
    proof
        have model.not_both c m t
        have decided_of c m (atoms cl)
        match term.structure t
            ConstOf b     ->
                have model.const_meaning c m t b
                have model.holds_is c m t
            NotOf a       ->
                have model.not_meaning c m t a
                have model.not_both c m a
            AndOf ps      ->
                have model.and_meaning c m t ps
                if which == 0
                    have atoms_no ps
                    if model.holds c m t then auto else have some_false c m ps
                else
                    match list.head (list.drop (which - 1) ps)
                        Some p ->
                            if model.holds c m t then have nth_holds c m ps (which - 1) p else auto
                        None   -> auto
            OrOf ps       ->
                have model.or_meaning c m t ps
                if which == 0
                    have atoms_yes ps
                    if model.holds c m t then have some_true c m ps else auto
                else
                    match list.head (list.drop (which - 1) ps)
                        Some p ->
                            have model.not_both c m p
                            if model.holds c m p then have nth_holds_one c m ps (which - 1) p else auto
                        None   -> auto
            ImpliesOf a b ->
                have model.implies_meaning c m t a b
                have model.not_both c m a
                have model.not_both c m b
            IteOf p a b   ->
                have model.ite_meaning c m t p a b
                have model.holds_is c m t
                have model.holds_is c m a
                have model.holds_is c m b
                have model.not_both c m p
                have model.not_both c m a
                have model.not_both c m b
            IffOf a b     ->
                have model.iff_meaning c m t a b
                have model.not_both c m a
                have model.not_both c m b
            _             -> auto

lemma fact_holds c m fs k f : c~Context, m~Model, fs~List Term, k~Nat, f~Term, model.holds_all c m fs,
                              list.head (list.drop k fs) == Some f
    ensures model.holds c m f
    proof
        have nth_holds c m fs k f

# The atoms in front of a list of terms that all have values have values.
lemma valued_front c m xs ys : c~Context, m~Model, xs~List Term, ys~List Term,
                               defined: (forall t : t~Term, list.contains (xs ++ ys) t, model.has_value c m t)
    ensures valued c m xs
    proof
        match xs
            []        -> auto
            x :: rest ->
                have defined x
                have valued_front c m rest ys

lemma defined_back c m xs ys : c~Context, m~Model, xs~List Term, ys~List Term,
                               defined: (forall t : t~Term, list.contains (xs ++ ys) t, model.has_value c m t)
    ensures forall t : t~Term, list.contains ys t implies model.has_value c m t
    proof
        have list.contains_append xs ys t
        have defined t

# The clause a right step adds is true, where the goal isn't.
lemma step_sound c goal m db s cl : c~Context, goal~Term, m~Model, db~List (List Lit), s~Step, cl~List Lit,
                                    step_clause c goal s == Some cl, model.booleans c (atoms cl), step_ok c db s cl,
                                    valued c m (atoms cl), db_holds c m db, model.holds_all c m (term.facts c),
                                    not (model.holds c m goal)
    ensures clause_holds c m cl
    proof
        match s
            Fact k               ->
                match list.head (list.drop k (term.facts c))
                    Some f -> have fact_holds c m (term.facts c) k f
                    None   -> auto
            NotGoal              -> have model.two_valued c m goal
            Structure t which    -> have structure_sound c m t which cl
            Resolve clause hints -> have resolve_sound c m db cl hints

# Running the steps from true clauses adds only true clauses, where the goal
# isn't true.
lemma run_sound c goal m db steps out : c~Context, goal~Term, m~Model, db~List (List Lit), steps~List Step,
                                        out~List (List Lit), run c goal db steps == Some out, db_holds c m db,
                                        model.holds_all c m (term.facts c), not (model.holds c m goal),
                                        defined: (forall t : t~Term, list.contains (terms_of c goal steps) t,
                                                  model.has_value c m t)
    ensures db_holds c m out
    proof
        match steps
            []        -> auto
            s :: rest ->
                match step_clause c goal s
                    Some cl ->
                        have valued_front c m (atoms cl) (terms_of c goal rest)
                        have defined_back c m (atoms cl) (terms_of c goal rest)
                        have step_sound c goal m db s cl
                        have run_sound c goal m (cl :: db) rest out
                    None    -> auto

# ── The statement ────────────────────────────────────────────────────────────

# Whether `v` is the value in `m` of one of `ts`.
export transparent fn value_among c m ts v -> r : c~Context, m~Model, ts~List Term, v~Value, r~Bool
    match ts
        []        -> False
        t :: rest -> model.eval c m t == Ok v or value_among c m rest v

# Whether each of `vs` is the value in `m` of one of `ts`.
export transparent fn values_among c m ts vs -> r : c~Context, m~Model, ts~List Term, vs~List Value, r~Bool
    match vs
        []        -> True
        v :: rest -> value_among c m ts v and values_among c m ts rest

# If `checks` accepts `refutation`, the goal is true in every model `m` where
#
# - `facts`: every fact of `c` is true;
# - `defined`: every term `refutation` uses has a value of its sort (a model
#   whose functions answer wherever these terms need them);
# - `axioms`, `definitions`: each axiom of `c`, and each definition's
#   equation, holds at the values of the terms `refutation` uses;
# - `arrays`: the array laws hold, and the model answers, at those values
#   (`model.arrays_ok_at`, `model.arrays_total_at`).
#
# Why this isn't vacuous, an argument outside Checkers (as `smt.model`'s
# header gives it): `checks` requires every term used to be a closed `Bool`
# term of `c`, so in any SMT-LIB model of `c` each has a value; that model,
# restricted to the finitely many values these terms need, is a `Model`
# meeting every premise. In Checkers, `cert_checks` builds one such model
# for an accepted refutation, and `axiom_premises_ok` shows that no axiom of
# `c` makes `axioms` unsatisfiable at no values. The same for definitions'
# equations (`model.definition_axiom`) waits for `term.sort_of`'s
# inversion lemmas (#85). Today's steps use only
# `facts` and `defined`; `axioms`, `definitions` and `arrays` are there for
# the theory steps to come (S6b–S6e), so that adding them doesn't change
# this statement.
export lemma checks_sound c goal refutation m : c~Context, goal~Term, refutation~Refutation, checks c goal refutation, m~Model,
                                                facts: model.holds_all c m (term.facts c),
                                                defined: (forall t : t~Term, list.contains (terms c goal refutation) t,
                                                          model.has_value c m t),
                                                axioms: (forall a vs : a~Axiom, vs~List Value, list.contains (term.axioms c) a,
                                                         values_among c m (terms c goal refutation) vs, model.holds_at c m a vs),
                                                definitions: (forall n d vs : n~Nat, d~Def, vs~List Value,
                                                              list.contains (term.defs c) (n, d), values_among c m (terms c goal refutation) vs,
                                                              model.holds_at c m (model.definition_axiom n d) vs),
                                                arrays: (forall s a b i j x env senv xs body : s~Sort, a~Nat, b~Nat, i~Value, j~Value,
                                                         x~Value, env~List Value, senv~List Sort, xs~Sort, body~Term,
                                                         values_among c m (terms c goal refutation) (ArrayElem a :: ArrayElem b :: i :: j :: x :: env),
                                                         model.arrays_ok_at c m s a b i j x env senv xs body
                                                         and model.arrays_total_at c m s a b i j x env senv xs body)
    ensures model.holds c m goal
    proof
        if model.holds c m goal
            auto
        else
            have defined_back c m [goal] (terms_of c goal refutation.steps)
            match run c goal [] refutation.steps
                Some out ->
                    have run_sound c goal m [] refutation.steps out
                    match out
                        last :: _ -> auto
                        []        -> auto
                None     -> auto

# A refutation `checks` accepts has steps. That its last clause is empty
# is `checks`' definition itself (transparent, above), and `cert_checks`
# checks both at examples; this lemma states the first.
export lemma checks_has_steps c goal refutation : c~Context, goal~Term, refutation~Refutation, checks c goal refutation
    ensures refutation.steps != []
    proof
        match refutation.steps
            []     -> auto
            _ :: _ -> auto

# The goal is among the terms a refutation uses, and so is every fact a
# `Fact` step cites: `defined` covers them.
export lemma goal_used c goal refutation : c~Context, goal~Term, refutation~Refutation
    ensures list.contains (terms c goal refutation) goal

export lemma fact_used c goal refutation k f : c~Context, goal~Term, refutation~Refutation, k~Nat, f~Term,
                                               list.contains refutation.steps (Fact k),
                                               list.head (list.drop k (term.facts c)) == Some f
    ensures list.contains (terms c goal refutation) f
    proof
        have fact_in_steps c goal refutation.steps k f

lemma fact_in_steps c goal steps k f : c~Context, goal~Term, steps~List Step, k~Nat, f~Term, list.contains steps (Fact k),
                                       list.head (list.drop k (term.facts c)) == Some f
    ensures list.contains (terms_of c goal steps) f
    proof
        match steps
            []        -> auto
            s :: rest ->
                if s == Fact k
                    auto
                else
                    have fact_in_steps c goal rest k f
                    match step_clause c goal s
                        Some cl -> have list.contains_append (atoms cl) (terms_of c goal rest) f
                        None    -> auto

# Every axiom of `c` is well-sorted in it, so `model.holds_at` evaluates it
# rather than being false: the `axioms` premise can be met.
export lemma axiom_premises_ok c a : c~Context, a~Axiom, list.contains (term.axioms c) a
    ensures term.axiom_ok c a
    proof
        have term.axioms_well_sorted c
        have term.axiom_listed c (term.axioms c) a

# `not fails` for a partial model: if `checks` accepts `refutation`, the
# goal isn't false in any model `m` that a model `n` meeting
# `checks_sound`'s premises extends (`model.monotone`: `n` says what `m`
# says wherever `m` says something, names `m`'s arrays, and has `m`'s
# elements). Every definite answer of `m` is `n`'s, and in `n` the goal
# holds.
export lemma not_refuted c goal refutation m n : c~Context, goal~Term, refutation~Refutation, checks c goal refutation,
                                                 m~Model, n~Model,
                                                 facts: model.holds_all c n (term.facts c),
                                                 defined: (forall t : t~Term, list.contains (terms c goal refutation) t,
                                                           model.has_value c n t),
                                                 axioms: (forall a vs : a~Axiom, vs~List Value, list.contains (term.axioms c) a,
                                                          values_among c n (terms c goal refutation) vs, model.holds_at c n a vs),
                                                 definitions: (forall d_n d vs : d_n~Nat, d~Def, vs~List Value,
                                                               list.contains (term.defs c) (d_n, d),
                                                               values_among c n (terms c goal refutation) vs,
                                                               model.holds_at c n (model.definition_axiom d_n d) vs),
                                                 arrays: (forall s a b i j x env senv xs body : s~Sort, a~Nat, b~Nat, i~Value,
                                                          j~Value, x~Value, env~List Value, senv~List Sort, xs~Sort, body~Term,
                                                          values_among c n (terms c goal refutation)
                                                          (ArrayElem a :: ArrayElem b :: i :: j :: x :: env),
                                                          model.arrays_ok_at c n s a b i j x env senv xs body
                                                          and model.arrays_total_at c n s a b i j x env senv xs body),
                                                 said: (forall q v : q~model.Asked, v~Value, model.said m q == Some v,
                                                        model.said n q == Some v),
                                                 named: (forall s k : s~Sort, k~Nat, m.array_in s k, n.array_in s k),
                                                 domains: (forall u args k : u~Nat, args~List Sort, k~Nat,
                                                           model.of_sort c m (term.Unin u args) (model.Element k),
                                                           model.of_sort c n (term.Unin u args) (model.Element k))
    ensures not (model.fails c m goal)
    proof
        have checks_sound c goal refutation n
        have model.holds_is c m goal
        have model.holds_is c n goal
        have model.not_both c n goal
        if model.fails c m goal
            have model.monotone c m n goal (model.Truth False)
        else
            auto
