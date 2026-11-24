# term.ck — sorts, terms and contexts: what the solver reasons about.
#
# A problem is a `Context` (declarations, recursive definitions, axioms and
# ground facts) and a goal. A `Context` can only be built by the functions
# here, and each of them checks what it adds, so every `Context` is
# well-sorted: every sort it mentions is declared with the right number of
# arguments, every term has a sort, every fact and axiom is a `Bool`, and
# every definition's body has its result sort (`check_all`).
#
# Declarations are numbered in the order they are made, and terms refer to
# them by number. Names are kept only to write a problem back out.

module term

import std.array
import std.list

# ── Names ────────────────────────────────────────────────────────────────────

# A symbol's characters. Written between bars or not (`|x|` or `x`), it is
# the same symbol.
export type Name = n~Bytes

# ── Sorts ────────────────────────────────────────────────────────────────────

# A sort. `Data d args` is the `d`-th datatype declared, `Unin u args` the
# `u`-th sort declared with `declare-sort`; each is applied to as many
# sorts as it has parameters. `Param k` is a datatype's `k`-th parameter,
# and appears only in the datatype's own declaration.
export enum Sort
    Bool
    Int
    Seq elem        : elem~Sort
    Arr index value : index~Sort, value~Sort
    Data d args     : d~Nat, args~List Sort
    Unin u args     : u~Nat, args~List Sort
    Param k         : k~Nat

# A sort declared with `declare-sort`, and how many arguments it takes.
export record SortDecl
    name~Name
    arity~Nat

# A constructor's field: its selector's name and its sort.
export record Field
    name~Name
    sort~Sort

# A constructor of a datatype. Its tester is `is-` and its name.
export record Ctor
    name~Name
    fields~List Field

# A datatype: its parameters' names (`par (T0 T1)`) and constructors.
# Field sorts may use `Param k` for `k` below the number of parameters.
export record Datatype
    name~Name
    params~List Name
    ctors~List Ctor

# How a function was introduced: `declare-fun`, `declare-const` (no
# parameters; the problem's unknowns), or a recursive definition.
export enum FunKind
    Declared
    Constant
    Defined

# A function's signature.
export record FunDecl
    name~Name
    params~List Sort
    result~Sort
    kind~FunKind

# ── Terms ────────────────────────────────────────────────────────────────────

# The built-in operations of the fragment `ckc` uses (SPEC §7.3).
export enum Op
    Not
    And
    Or
    Implies
    Ite
    Eq
    Add
    Sub
    Neg
    Mul
    Div
    Mod
    Lt
    Le
    Gt
    Ge
    Select
    Store
    MapAdd
    SeqLen
    SeqNth
    SeqUnit
    SeqConcat
    SeqExtract

# What a term applies. `Fun f` is the `f`-th function; `Con d k args` the
# `k`-th constructor of the `d`-th datatype, building a `Data d args`;
# `Is d k` its tester; `Sel d k j` the selector of its `j`-th field.
export enum Head
    Fun f        : f~Nat
    Con d k args : d~Nat, k~Nat, args~List Sort
    Is d k       : d~Nat, k~Nat
    Sel d k j    : d~Nat, k~Nat, j~Nat
    Num n        : n~Nat
    Boolean b    : b~Bool
    Prim op      : op~Op
    ConstArr s   : s~Sort
    EmptySeq s   : s~Sort

# A term. Variables are numbered from the innermost binder out (de Bruijn
# indices): binders bind left to right, so the last variable a `let`,
# `forall` or definition binds is `Var 0`. A `let` binds all its names at
# once; a `lambda` binds one variable and is an array from it.
export enum Term
    Var i           : i~Nat
    App head args   : head~Head, args~List Term
    Let binds body  : binds~List (Name, Term), body~Term
    Lam name s body : name~Name, s~Sort, body~Term

# ── Definitions and axioms ───────────────────────────────────────────────────

# A recursive definition: `define-fun-rec`. `terminates` is the caller's
# promise that the body terminates at every argument of its parameters'
# sorts, in every interpretation of the declared functions, so that the
# definition has exactly one solution. It is trusted only for
# counterexamples (`model.refutes`); `ckc` owes it (#299), and `parse`
# marks none.
export record Def
    name~Name
    params~List (Name, Sort)
    result~Sort
    body~Term
    terminates~Bool

# A universal formula: `forall vars, body`. Each of `patterns` is a list of
# terms that must all match for E-matching to make an instance.
#
# With `patterns = []` the axiom is still a fact of the problem; it only
# gives E-matching nothing to match, so it is never instantiated that way.
# A later stage may instantiate it at ground terms of its variables' sorts:
# an instance is a consequence, so a proof that uses one is sound. It must
# not be dropped, and a problem holding one is never answered `Invalid`
# unless the model is shown to satisfy it.
export record Axiom
    vars~List (Name, Sort)
    body~Term
    patterns~List (List Term)

# One step of building a problem, as SMT-LIB writes it.
export enum Command
    DeclareSort decl       : decl~SortDecl
    DeclareDatatypes ds    : ds~List Datatype
    DeclareFun f           : f~FunDecl
    # `define-fun-rec` (`single`) or `define-funs-rec`: definitions that may
    # use each other.
    DefineFuns single defs : single~Bool, defs~List Def
    Assume a               : a~Axiom
    Assert t               : t~Term

# ── Signatures ───────────────────────────────────────────────────────────────

# Everything declared so far, numbered in order. `values` holds, for each
# datatype, a value of it found when it was declared (`Witness`; see
# "Datatypes with values"): kept so that later declarations need not look
# again.
export record Sig
    sorts~Array SortDecl
    datatypes~Array Datatype
    funs~Array FunDecl
    values~Array Witness

export fn empty_sig -> s : s~Sig
    Sig (array.from_list []) (array.from_list []) (array.from_list []) (array.from_list [])

fn def_fun d -> f : d~Def, f~FunDecl
    FunDecl d.name (list.map (\(_, s) -> s) d.params) d.result Defined

fn def_funs ds -> fs : ds~List Def, fs~List FunDecl
    list.map def_fun ds

# The signature after `c`.
export fn extend sig c -> r : sig~Sig, c~Command, r~Sig
    match c
        DeclareSort d       -> Sig (sig.sorts ++ array.from_list [d]) sig.datatypes sig.funs sig.values
        DeclareDatatypes ds -> Sig sig.sorts (sig.datatypes ++ array.from_list ds) sig.funs (sig.values ++ array.from_list (group_values sig ds))
        DeclareFun f        -> Sig sig.sorts sig.datatypes (sig.funs ++ array.from_list [f]) sig.values
        DefineFuns _ ds     -> Sig sig.sorts sig.datatypes (sig.funs ++ array.from_list (def_funs ds)) sig.values
        Assume _            -> sig
        Assert _            -> sig

# The signature after all of `cs`.
export fn extend_all sig cs -> r : sig~Sig, cs~List Command, r~Sig
    match cs
        []        -> sig
        c :: rest -> extend_all (extend sig c) rest

# ── Problems ─────────────────────────────────────────────────────────────────

# Why a command can't be added: what is wrong, about which sort or head.
export enum Problem
    # A sort not declared, or applied to the wrong number of sorts.
    BadSort s           : s~Sort
    # A datatype without constructors.
    NoCtors d           : d~Datatype
    # A head that can't be applied to arguments of these sorts.
    BadApply head found : head~Head, found~List Sort
    # A variable no binder binds.
    Unbound i           : i~Nat
    # A `let` that binds nothing.
    EmptyLet
    # A constant with parameters.
    ConstantParams f    : f~FunDecl
    # Something of sort `found` where `want` is needed: a fact or axiom
    # that isn't a `Bool`, a definition's body that isn't its result sort.
    Expected want found : want~Sort, found~Sort
    # A pattern without terms.
    NoPattern
    # A datatype with no values: every constructor needs a value of a sort
    # that has none, such as the datatype itself.
    NotWellFounded d    : d~Datatype
    # A datatype in the index of an array in its own fields: there is no
    # such set.
    NotCovariant d      : d~Datatype

# ── Well-formed sorts ────────────────────────────────────────────────────────

# Whether `s` is a sort of `sig`, where `np` parameters may be used.
export transparent fn sort_ok sig np s -> r : sig~Sig, np~Nat, s~Sort, r~Bool
    match s
        Bool        -> True
        Int         -> True
        Seq e       -> sort_ok sig np e
        Arr i v     -> sort_ok sig np i and sort_ok sig np v
        Data d args ->
            d < len sig.datatypes and list.length args == list.length sig.datatypes[d].params
                and sorts_ok sig np args
        Unin u args -> u < len sig.sorts and list.length args == sig.sorts[u].arity and sorts_ok sig np args
        Param k     -> k < np

export transparent fn sorts_ok sig np ss -> r : sig~Sig, np~Nat, ss~List Sort, r~Bool
    match ss
        []        -> True
        s :: rest -> sort_ok sig np s and sorts_ok sig np rest

fn check_sort sig np s -> r : sig~Sig, np~Nat, s~Sort, r~Result Unit Problem
    if sort_ok sig np s then Ok () else Err (BadSort s)

fn check_sorts sig np ss -> r : sig~Sig, np~Nat, ss~List Sort, r~Result Unit Problem
    match ss
        []        -> Ok ()
        s :: rest ->
            let _ = try check_sort sig np s
            check_sorts sig np rest

# `s` with each `Param k` replaced by the `k`-th of `args`.
export fn instantiate args s -> r : args~List Sort, s~Sort, r~Sort
    match s
        Bool      -> Bool
        Int       -> Int
        Seq e     -> Seq (instantiate args e)
        Arr i v   -> Arr (instantiate args i) (instantiate args v)
        Data d ss -> Data d (list.map (instantiate args) ss)
        Unin u ss -> Unin u (list.map (instantiate args) ss)
        Param k   ->
            match list.head (list.drop k args)
                Some a -> a
                None   -> Param k

# ── Sorts of terms ───────────────────────────────────────────────────────────

# The `k`-th constructor of the `d`-th datatype, if there is one.
export transparent fn ctor sig d k -> r : sig~Sig, d~Nat, k~Nat, r~Option Ctor
    if d < len sig.datatypes then list.head (list.drop k sig.datatypes[d].ctors) else None

export transparent fn field_sorts fs -> r : fs~List Field, r~List Sort
    match fs
        []        -> []
        f :: rest -> f.sort :: field_sorts rest

# The sort a head gives when applied to arguments of sorts `found`.
export fn apply_sort sig h found -> r : sig~Sig, h~Head, found~List Sort, r~Result Sort Problem
    let bad = Err (BadApply h found)
    match h
        Fun f        ->
            if f < len sig.funs and sig.funs[f].params == found then Ok sig.funs[f].result else bad
        Con d k args ->
            match ctor sig d k
                Some c if sort_ok sig 0 (Data d args)
                    and list.map (instantiate args) (field_sorts c.fields) == found -> Ok (Data d args)
                _ -> bad
        Is d k       ->
            match (ctor sig d k, found)
                (Some _, [Data e _]) if e == d -> Ok Bool
                _ -> bad
        Sel d k j    ->
            match (ctor sig d k, found)
                (Some c, [Data e args]) if e == d ->
                    match list.head (list.drop j c.fields)
                        Some f -> Ok (instantiate args f.sort)
                        None   -> bad
                _ -> bad
        Num _        -> if found == [] then Ok Int else bad
        Boolean _    -> if found == [] then Ok Bool else bad
        ConstArr s   ->
            match s
                Arr _ v if sort_ok sig 0 s and found == [v] -> Ok s
                _ -> bad
        EmptySeq s   ->
            match s
                Seq _ if sort_ok sig 0 s and found == [] -> Ok s
                _ -> bad
        Prim op      ->
            match prim_sort op found
                Some s -> Ok s
                None   -> bad

# The sort a built-in operation gives for arguments of sorts `found`.
fn prim_sort op found -> r : op~Op, found~List Sort, r~Option Sort
    match op
        Not        -> if found == [Bool] then Some Bool else None
        And        -> if list.length found >= 2 and list.all (\s -> s == Bool) found then Some Bool else None
        Or         -> if list.length found >= 2 and list.all (\s -> s == Bool) found then Some Bool else None
        Implies    -> if found == [Bool, Bool] then Some Bool else None
        Ite        ->
            match found
                [c, a, b] if c == Bool and a == b -> Some a
                _ -> None
        Eq         ->
            match found
                [a, b] if a == b -> Some Bool
                _ -> None
        Add        -> int2 found Int
        Sub        -> int2 found Int
        Mul        -> int2 found Int
        Div        -> int2 found Int
        Mod        -> int2 found Int
        Neg        -> if found == [Int] then Some Int else None
        Lt         -> int2 found Bool
        Le         -> int2 found Bool
        Gt         -> int2 found Bool
        Ge         -> int2 found Bool
        Select     ->
            match found
                [Arr i v, j] if i == j -> Some v
                _ -> None
        Store      ->
            match found
                [Arr i v, j, w] if i == j and v == w -> Some (Arr i v)
                _ -> None
        MapAdd     ->
            match found
                [Arr i v, Arr j w] if i == j and v == Int and w == Int -> Some (Arr i Int)
                _ -> None
        SeqLen     ->
            match found
                [Seq _] -> Some Int
                _       -> None
        SeqNth     ->
            match found
                [Seq e, i] if i == Int -> Some e
                _ -> None
        SeqUnit    ->
            match found
                [e] -> Some (Seq e)
                _   -> None
        SeqConcat  ->
            match found
                Seq e :: rest if rest != [] and list.all (\s -> s == Seq e) rest -> Some (Seq e)
                _ -> None
        SeqExtract ->
            match found
                [Seq e, i, n] if i == Int and n == Int -> Some (Seq e)
                _ -> None

fn int2 found r -> s : found~List Sort, r~Sort, s~Option Sort
    if found == [Int, Int] then Some r else None

# The sort of `t` in `sig`, where `env` gives the sorts of the bound
# variables (`Var 0` first).
export fn sort_of sig env t -> r : sig~Sig, env~List Sort, t~Term, r~Result Sort Problem
    match t
        Var i          ->
            match list.head (list.drop i env)
                Some s -> Ok s
                None   -> Err (Unbound i)
        App h args     ->
            let found = try sorts_of sig env args
            apply_sort sig h found
        Let binds body ->
            if binds == []
                Err EmptyLet
            else
                let ss = try bound_sorts sig env binds
                sort_of sig (list.reverse ss ++ env) body
        Lam _ s body   ->
            let _ = try check_sort sig 0 s
            let b = try sort_of sig (s :: env) body
            Ok (Arr s b)

export fn sorts_of sig env ts -> r : sig~Sig, env~List Sort, ts~List Term, r~Result (List Sort) Problem
    match ts
        []        -> Ok []
        t :: rest ->
            let s = try sort_of sig env t
            let ss = try sorts_of sig env rest
            Ok (s :: ss)

fn bound_sorts sig env bs -> r : sig~Sig, env~List Sort, bs~List (Name, Term), r~Result (List Sort) Problem
    match bs
        []             -> Ok []
        (_, t) :: rest ->
            let s = try sort_of sig env t
            let ss = try bound_sorts sig env rest
            Ok (s :: ss)

# Whether `t` has sort `want` in `sig` and `env`.
export fn check_term sig env t want -> r : sig~Sig, env~List Sort, t~Term, want~Sort, r~Result Unit Problem
    let s = try sort_of sig env t
    if s == want then Ok () else Err (Expected want s)

# ── Well-formed commands ─────────────────────────────────────────────────────

export transparent fn var_sorts vs -> r : vs~List (Name, Sort), r~List Sort
    match vs
        []             -> []
        (_, s) :: rest -> s :: var_sorts rest

# The environment of a binder list's body: the last variable is `Var 0`.
export fn binder_env vs -> r : vs~List (Name, Sort), r~List Sort
    list.reverse (var_sorts vs)

fn check_ctors sig np cs -> r : sig~Sig, np~Nat, cs~List Ctor, r~Result Unit Problem
    match cs
        []        -> Ok ()
        c :: rest ->
            let _ = try check_sorts sig np (field_sorts c.fields)
            check_ctors sig np rest

fn check_datatypes sig ds -> r : sig~Sig, ds~List Datatype, r~Result Unit Problem
    match ds
        []        -> Ok ()
        d :: rest ->
            if d.ctors == []
                Err (NoCtors d)
            else
                let _ = try check_ctors sig (list.length d.params) d.ctors
                check_datatypes sig rest

fn check_sigs sig ds -> r : sig~Sig, ds~List Def, r~Result Unit Problem
    match ds
        []        -> Ok ()
        d :: rest ->
            let _ = try check_sorts sig 0 (var_sorts d.params)
            let _ = try check_sort sig 0 d.result
            check_sigs sig rest

fn check_bodies sig ds -> r : sig~Sig, ds~List Def, r~Result Unit Problem
    match ds
        []        -> Ok ()
        d :: rest ->
            let _ = try check_term sig (binder_env d.params) d.body d.result
            check_bodies sig rest

fn check_patterns sig env ps -> r : sig~Sig, env~List Sort, ps~List (List Term), r~Result Unit Problem
    match ps
        []        -> Ok ()
        p :: rest ->
            if p == []
                Err NoPattern
            else
                let _ = try sorts_of sig env p
                check_patterns sig env rest

# ── Datatypes with values ────────────────────────────────────────────────────
# Every sort must have a value (SMT-LIB 2.6, §5.3: a structure's domains are
# non-empty). `check_values` asks two things of the datatypes one
# `declare-datatypes` declares (the group).
#
# 1. **Each has a value, shown by one.** A datatype is accepted only with a
#    `Witness`: a value built from its constructors, in which its
#    parameters may stand for values of the sorts they will be. `fits`
#    checks a witness against the datatype's sort, by structure alone, and
#    that check is what acceptance rests on: whatever the search below
#    does, a datatype is accepted only if `fits` holds of the witness it
#    found, so a sort with no values can't be accepted.
#
#    The search: whether `(D a1 … an)` has a value depends only on which
#    of `a1 … an` do. So it looks for a witness for each pair (`Shape`) of
#    a datatype that can be reached from the group and a choice of which of
#    its parameters have values: rounds, each adding every shape with a
#    constructor whose fields all have witnesses from the shapes found so
#    far, until a round adds none. That is the least fixed point of "has a
#    value"; each round takes shapes out of the finite list of those not
#    yet found, so the rounds end (`decreasing` on that list).
#
# 2. **None is in an array's index in its own group** (see
#    `in_index_check`): not written there, and not through a parameter of
#    a datatype that puts the parameter in an index. With arrays as all
#    functions (the standard interpretation), `T = mk (Array T Int)` would
#    need as many values as functions from `T` to `Int`, and there is no
#    such set (Cantor). Z3 rejects these too ("datatype is not co-variant").
#    In an array's values or in a sequence, a datatype is a tree with many
#    branches, which exists. An uninterpreted sort constructor applied to
#    the datatype doesn't count: its interpretation may ignore its
#    arguments, so `(Array (U T) Int)` has one.
#
# Z3 is less exact about values: it rejects `T = mk (Seq T)`, which has
# `(mk [])`, and accepts `(U T)` through `(Box (U T))` in one group, which
# has none.

# A value of a sort in which parameters may stand: `true`, `0`, the empty
# sequence, an uninterpreted sort's first element, the constant array of a
# value, parameter `k`'s value, constructor `k` applied to fields, or the
# witness kept for datatype `e` (declared in an earlier command) at the
# arguments' values.
export enum Witness
    WTrue
    WZero
    WEmpty
    WElement
    WConst v      : v~Witness
    WParam k      : k~Nat
    WCon k fields : k~Nat, fields~List Witness
    WOf e args    : e~Nat, args~List Witness

# Whether `w` is a value of sort `s` of `sig`, whatever values the
# parameters below `np` stand for, where the datatypes numbered below
# `first` were accepted before. This is the statement acceptance rests on:
# a datatype with a witness that fits its sort has a value for every choice
# of values for its parameters. `WOf e ws` fits `(e args)` when `e` was
# accepted before and each of `ws` fits its argument: `e`'s kept witness
# fitted `e`'s sort when it was accepted (`check_values`, for every
# `declare-datatypes` of a `Context`), so it fits at these arguments.
export fn fits sig first np w s -> r : sig~Sig, first~Nat, np~Nat, w~Witness, s~Sort, r~Bool
    match (w, s)
        (WTrue, Bool)            -> True
        (WZero, Int)             -> True
        (WEmpty, Seq _)          -> True
        (WElement, Unin _ _)     -> True
        (WConst v, Arr _ e)      -> fits sig first np v e
        (WParam k, Param j)      -> k == j and k < np
        (WCon k fs, Data d args) ->
            match ctor sig d k
                Some c ->
                    list.length args == list.length sig.datatypes[d].params
                        and fits_all sig first np fs (list.map (instantiate args) (field_sorts c.fields))
                None   -> False
        (WOf e ws, Data d args)  ->
            e == d and e < first and e < len sig.datatypes
                and list.length args == list.length sig.datatypes[e].params and fits_all sig first np ws args
        _                        -> False

fn fits_all sig first np ws ss -> r : sig~Sig, first~Nat, np~Nat, ws~List Witness, ss~List Sort, r~Bool
    match (ws, ss)
        ([], [])           -> True
        (w :: wr, s :: sr) -> fits sig first np w s and fits_all sig first np wr sr
        _                  -> False

# ── Lists that shrink ────────────────────────────────────────────────────────

# `xs` sorted by `f`: those it gives something for, with what, and the
# rest.
record Picked a b : a~Type, b~Type
    got~List (a, b)
    left~List a

fn pick f xs -> r : f~(a -> Option b), xs~List a, r~Picked a b
    match xs
        []        -> Picked [] []
        x :: rest ->
            let p = pick f rest
            match f x
                Some y -> Picked ((x, y) :: p.got) p.left
                None   -> Picked p.got (x :: p.left)

# Every element goes one way or the other: when something is picked, fewer
# are left.
lemma pick_length f xs : f~(a -> Option b), xs~List a
    ensures list.length (pick f xs).got + list.length (pick f xs).left == list.length xs
    proof
        match xs
            []        -> auto
            _ :: rest -> have pick_length f rest

# ── The search for witnesses ─────────────────────────────────────────────────

# A datatype, and whether each of its parameters has a value.
type Shape = sh~(Nat, List Bool)

# Whether `xs` is at most `ys`, place by place (`False` before `True`).
fn at_most xs ys -> r : xs~List Bool, ys~List Bool, r~Bool
    match (xs, ys)
        ([], [])           -> True
        (x :: xr, y :: yr) -> (not x or y) and at_most xr yr
        _                  -> False

# A witness found for `e` with parameters `bits` or fewer having values.
fn found_in found e bits -> r : found~List (Shape, Witness), e~Nat, bits~List Bool, r~Option Witness
    match found
        []                  -> None
        ((d, b), w) :: rest -> if d == e and at_most b bits then Some w else found_in rest e bits

# `w` with parameter `j` replaced by the `j`-th of `args`.
fn subst w args -> r : w~Witness, args~List Witness, r~Witness
    match w
        WConst v  -> WConst (subst v args)
        WParam j  ->
            match list.head (list.drop j args)
                Some a -> a
                None   -> WParam j
        WCon k fs -> WCon k (subst_all fs args)
        WOf e ws  -> WOf e (subst_all ws args)
        other     -> other

fn subst_all ws args -> r : ws~List Witness, args~List Witness, r~List Witness
    match ws
        []        -> []
        w :: rest -> subst w args :: subst_all rest args

# A witness for `s`, from the shapes found, where parameter `k` has one if
# `bits` says so.
fn witness stored first found bits s -> r : stored~Array Witness, first~Nat, found~List (Shape, Witness), bits~List Bool, s~Sort, r~Option Witness
    match s
        Bool        -> Some WTrue
        Int         -> Some WZero
        Seq _       -> Some WEmpty
        Unin _ _    -> Some WElement
        Arr _ v     ->
            match witness stored first found bits v
                Some w -> Some (WConst w)
                None   -> None
        Param k     ->
            match list.head (list.drop k bits)
                Some True -> Some (WParam k)
                _         -> None
        Data e args ->
            let ws = witnesses stored first found bits args
            match all_some ws
                Some vs if e < first and e < len stored -> Some (WOf e vs)
                _ ->
                    match found_in found e (have_all ws)
                        Some w -> Some (subst w (or_params ws))
                        None   -> None

fn witnesses stored first found bits ss -> r : stored~Array Witness, first~Nat, found~List (Shape, Witness), bits~List Bool, ss~List Sort, r~List (Option Witness)
    match ss
        []        -> []
        s :: rest -> witness stored first found bits s :: witnesses stored first found bits rest

fn have_all ws -> r : ws~List (Option Witness), r~List Bool
    match ws
        []             -> []
        Some _ :: rest -> True :: have_all rest
        None :: rest   -> False :: have_all rest

# The witnesses, with a parameter standing where there is none (only where
# `found_for` chose a witness that doesn't use it).
fn or_params ws -> r : ws~List (Option Witness), r~List Witness
    match ws
        []             -> []
        Some w :: rest -> w :: or_params rest
        None :: rest   -> WParam 0 :: or_params rest

fn all_some ws -> r : ws~List (Option Witness), r~Option (List Witness)
    match ws
        []             -> Some []
        Some w :: rest ->
            match all_some rest
                Some vs -> Some (w :: vs)
                None    -> None
        None :: _      -> None

# A witness for the shape: its first constructor whose fields all have one.
fn shape_witness sig first found sh -> r : sig~Sig, first~Nat, found~List (Shape, Witness), sh~Shape, r~Option Witness
    let (e, bits) = sh
    if e < len sig.datatypes then ctor_witness sig.values first found bits sig.datatypes[e].ctors 0 else None

fn ctor_witness stored first found bits cs k -> r : stored~Array Witness, first~Nat, found~List (Shape, Witness),
                                                    bits~List Bool, cs~List Ctor, k~Nat, r~Option Witness
    match cs
        []        -> None
        c :: rest ->
            match all_some (witnesses stored first found bits (field_sorts c.fields))
                Some ws -> Some (WCon k ws)
                None    -> ctor_witness stored first found bits rest (k + 1)

# The least fixed point: rounds over the shapes not yet found, until a
# round finds none. A round that finds one leaves fewer (`pick_length`).
fn fixed sig first found todo -> r : sig~Sig, first~Nat, found~List (Shape, Witness), todo~List Shape,
                                     r~List (Shape, Witness)
    decreasing list.length todo
    let next = pick (shape_witness sig first found) todo
    have pick_length (shape_witness sig first found) todo
    match next.got
        []     -> found
        _ :: _ -> fixed sig first (found ++ next.got) next.left

# ── The shapes to search ─────────────────────────────────────────────────────

# The datatypes `s` applies to arguments that mention a parameter or a
# datatype numbered `first` or after: only through those can a parameter or
# a datatype of the group be without a value. (A datatype declared before,
# applied otherwise, has its kept witness.)
fn flows_in first s -> r : first~Nat, s~Sort, r~List Nat
    match s
        Bool        -> []
        Int         -> []
        Seq e       -> flows_in first e
        Arr i v     -> flows_in first i ++ flows_in first v
        Data e args -> (if any_open first args then [e] else []) ++ all_flows_in first args
        Unin _ args -> all_flows_in first args
        Param _     -> []

fn all_flows_in first ss -> r : first~Nat, ss~List Sort, r~List Nat
    match ss
        []        -> []
        s :: rest -> flows_in first s ++ all_flows_in first rest

# Whether `s` mentions a parameter or a datatype numbered `first` or after.
fn open_sort first s -> r : first~Nat, s~Sort, r~Bool
    match s
        Bool        -> False
        Int         -> False
        Seq e       -> open_sort first e
        Arr i v     -> open_sort first i or open_sort first v
        Data e args -> e >= first or any_open first args
        Unin _ args -> any_open first args
        Param _     -> True

fn any_open first ss -> r : first~Nat, ss~List Sort, r~Bool
    match ss
        []        -> False
        s :: rest -> open_sort first s or any_open first rest

fn ctors_fields cs -> r : cs~List Ctor, r~List Sort
    match cs
        []        -> []
        c :: rest -> field_sorts c.fields ++ ctors_fields rest

fn fields_of sig e -> r : sig~Sig, e~Nat, r~List Sort
    if e < len sig.datatypes then ctors_fields sig.datatypes[e].ctors else []

fn flows_from sig first xs -> r : sig~Sig, first~Nat, xs~List Nat, r~List Nat
    match xs
        []        -> []
        x :: rest -> all_flows_in first (fields_of sig x) ++ flows_from sig first rest

fn is_named named x -> r : named~List Nat, x~Nat, r~Option Unit
    if list.contains named x then Some () else None

# The datatypes a parameter or the group can flow into from `frontier`
# (and those before it, `reached`): rounds that take from `rest`, those
# not yet reached, until a round takes none.
fn relevant sig first reached frontier rest -> r : sig~Sig, first~Nat, reached~List Nat, frontier~List Nat,
                                                   rest~List Nat, r~List Nat
    decreasing list.length rest
    let named = flows_from sig first frontier
    let next = pick (is_named named) rest
    have pick_length (is_named named) rest
    match next.got
        []        -> reached
        x :: more ->
            have list.length next.got == 1 + list.length more
            relevant sig first (reached ++ list.keys next.got) (list.keys next.got) next.left

# `count` numbers from `i`.
fn upto count i -> r : count~Nat, i~Nat, r~List Nat
    if count == 0 then [] else i :: upto (count - 1) (i + 1)

# Every choice of `True` and `False` for `n` places.
fn choices n -> r : n~Nat, r~List (List Bool)
    if n == 0
        [[]]
    else
        let rest = choices (n - 1)
        list.map (\c -> True :: c) rest ++ list.map (\c -> False :: c) rest

fn shapes_of sig es -> r : sig~Sig, es~List Nat, r~List Shape
    match es
        []        -> []
        e :: rest ->
            let n = if e < len sig.datatypes then list.length sig.datatypes[e].params else 0
            list.map (\b -> (e, b)) (choices n) ++ shapes_of sig rest

# ── Arrays' indices ──────────────────────────────────────────────────────────

# A place: datatype `e`'s `k`-th parameter.
type Place = pl~(Nat, Nat)

# Whether, in `s`, a parameter in `ks` is in an array's index (`inside`:
# `s` itself is), through `in_place` for the parameters of datatypes.
# `Unin` arguments don't count (see above).
fn param_in_index in_place ks s inside -> r : in_place~(Nat -> Nat -> Bool), ks~List Nat, s~Sort, inside~Bool,
                                              r~Bool
    match s
        Bool        -> False
        Int         -> False
        Seq e       -> param_in_index in_place ks e inside
        Arr i v     -> param_in_index in_place ks i True or param_in_index in_place ks v inside
        Data e args -> args_in_index in_place ks e args 0 inside
        Unin _ _    -> False
        Param k     -> inside and list.contains ks k

fn args_in_index in_place ks e args j inside -> r : in_place~(Nat -> Nat -> Bool), ks~List Nat, e~Nat,
                                                    args~List Sort, j~Nat, inside~Bool, r~Bool
    match args
        []        -> False
        a :: rest ->
            param_in_index in_place ks a (inside or in_place e j) or args_in_index in_place ks e rest (j + 1) inside

# Whether a datatype in `group` is in an array's index in `s`, by the same
# rules.
fn group_in_index in_place group s inside -> r : in_place~(Nat -> Nat -> Bool), group~List Nat, s~Sort,
                                                 inside~Bool, r~Bool
    match s
        Bool        -> False
        Int         -> False
        Seq e       -> group_in_index in_place group e inside
        Arr i v     -> group_in_index in_place group i True or group_in_index in_place group v inside
        Data e args -> (inside and list.contains group e) or group_args_index in_place group e args 0 inside
        Unin _ _    -> False
        Param _     -> False

fn group_args_index in_place group e args j inside -> r : in_place~(Nat -> Nat -> Bool), group~List Nat, e~Nat,
                                                          args~List Sort, j~Nat, inside~Bool, r~Bool
    match args
        []        -> False
        a :: rest ->
            group_in_index in_place group a (inside or in_place e j)
                or group_args_index in_place group e rest (j + 1) inside

fn all_places sig es -> r : sig~Sig, es~List Nat, r~List Place
    match es
        []        -> []
        e :: rest ->
            let n = if e < len sig.datatypes then list.length sig.datatypes[e].params else 0
            list.map (\k -> (e, k)) (upto n 0) ++ all_places sig rest

fn any_in_index sig in_place e k ss -> r : sig~Sig, in_place~(Nat -> Nat -> Bool), e~Nat, k~Nat, ss~List Sort, r~Bool
    match ss
        []        -> False
        s :: rest -> param_in_index in_place [k] s False or any_in_index sig in_place e k rest

# The places whose parameter is in an array's index: rounds that take from
# `rest` those found, given those found so far, until none is.
fn index_places sig found rest -> r : sig~Sig, found~List Place, rest~List Place, r~List Place
    decreasing list.length rest
    let next = pick (is_in sig found) rest
    have pick_length (is_in sig found) rest
    match next.got
        []     -> found
        _ :: _ -> index_places sig (found ++ list.keys next.got) next.left

fn is_in sig found pl -> r : sig~Sig, found~List Place, pl~Place, r~Option Unit
    let (e, k) = pl
    if any_in_index sig (\d j -> list.contains found (d, j)) e k (fields_of sig e) then Some () else None

# The first of `ds` (numbered from `first`) with a datatype of its group in
# an array's index in a field.
fn in_index_check sig first ds reach -> r : sig~Sig, first~Nat, ds~List Datatype, reach~List Nat, r~Option Datatype
    let group = upto (list.length ds) first
    let places = index_places sig [] (all_places sig reach)
    let in_place = \e k -> list.contains places (e, k)
    first_in_index in_place group ds

fn first_in_index in_place group ds -> r : in_place~(Nat -> Nat -> Bool), group~List Nat, ds~List Datatype,
                                           r~Option Datatype
    match ds
        []        -> None
        d :: rest ->
            if any_group_in_index in_place group (ctors_fields d.ctors)
                Some d
            else
                first_in_index in_place group rest

fn any_group_in_index in_place group ss -> r : in_place~(Nat -> Nat -> Bool), group~List Nat, ss~List Sort, r~Bool
    match ss
        []        -> False
        s :: rest -> group_in_index in_place group s False or any_group_in_index in_place group rest

# ── The check ────────────────────────────────────────────────────────────────

fn trues n -> r : n~Nat, r~List Bool
    if n == 0 then [] else True :: trues (n - 1)

fn params_of count i -> r : count~Nat, i~Nat, r~List Sort
    if count == 0 then [] else Param i :: params_of (count - 1) (i + 1)

# The datatypes that matter for the group of `ds`, numbered from `first`
# in `sig`: the group, and those a parameter or the group flows into.
fn group_reach sig first ds -> r : sig~Sig, first~Nat, ds~List Datatype, r~List Nat
    let group = upto (list.length ds) first
    if flows_from sig first group == []
        group
    else
        let others = pick (\x -> if list.contains group x then None else Some ()) (upto (len sig.datatypes) 0)
        relevant sig first group group (list.keys others.got)

# A witness for each of `ds`, declared after `sig`, with all its parameters
# having values; `WTrue` (which fits no datatype) where none was found.
export fn group_values sig ds -> r : sig~Sig, ds~List Datatype, r~List Witness
    let first = len sig.datatypes
    let big = Sig sig.sorts (sig.datatypes ++ array.from_list ds) sig.funs sig.values
    let found = fixed big first [] (shapes_of big (group_reach big first ds))
    each_value big.values first found ds 0

fn each_value stored first found ds i -> r : stored~Array Witness, first~Nat, found~List (Shape, Witness),
                                             ds~List Datatype, i~Nat, r~List Witness
    match ds
        []        -> []
        d :: rest ->
            let w =
                match found_in found (first + i) (trues (list.length d.params))
                    Some x -> x
                    None   -> WTrue
            w :: each_value stored first found rest (i + 1)

# Whether `ds`, the datatypes of `sig` numbered from `first` (`sig` is the
# signature after them), each have a value and are in no array's index in
# their group's fields. Acceptance rests on `fits` of the kept witness.
fn check_values sig first ds -> r : sig~Sig, first~Nat, ds~List Datatype, r~Result Unit Problem
    match in_index_check sig first ds (group_reach sig first ds)
        Some d -> Err (NotCovariant d)
        None   ->
            match first_unfit sig first ds 0
                Some d -> Err (NotWellFounded d)
                None   -> Ok ()

fn first_unfit sig first ds i -> r : sig~Sig, first~Nat, ds~List Datatype, i~Nat, r~Option Datatype
    match ds
        []        -> None
        d :: rest ->
            let n = list.length d.params
            let e = first + i
            let ok = e < len sig.values and fits sig first n sig.values[e] (Data e (params_of n 0))
            if ok then first_unfit sig first rest (i + 1) else Some d

# Whether `c` is well-formed after the commands that gave `sig`.
export fn check_command sig c -> r : sig~Sig, c~Command, r~Result Unit Problem
    match c
        DeclareSort _       -> Ok ()
        DeclareDatatypes ds ->
            let _ = try check_datatypes (extend sig c) ds
            check_values (extend sig c) (len sig.datatypes) ds
        DeclareFun f        ->
            match f.kind
                Constant if f.params != [] -> Err (ConstantParams f)
                _ ->
                    let _ = try check_sorts sig 0 f.params
                    check_sort sig 0 f.result
        DefineFuns _ ds     ->
            let _ = try check_sigs sig ds
            check_bodies (extend sig c) ds
        Assume a            ->
            let _ = try check_sorts sig 0 (var_sorts a.vars)
            let env = binder_env a.vars
            let _ = try check_term sig env a.body Bool
            check_patterns sig env a.patterns
        Assert t            -> check_term sig [] t Bool

# Whether each of `cs` is well-formed after `sig` and the commands before it.
export fn check_all sig cs -> r : sig~Sig, cs~List Command, r~Result Unit Problem
    match cs
        []        -> Ok ()
        c :: rest ->
            let _ = try check_command sig c
            check_all (extend sig c) rest

# ── Contexts ─────────────────────────────────────────────────────────────────

# A well-formed problem without its goal: its commands in order, and the
# signature they declare.
export abstract record Context
    commands~List Command
    sig~Sig, check_all empty_sig commands == Ok (), sig == extend_all empty_sig commands

# The context with nothing in it.
export fn empty -> c : c~Context
    Context [] empty_sig

# The commands, in order.
export fn commands c -> cs : c~Context, cs~List Command
    c.commands

# What the commands declare.
export fn signature c -> s : c~Context, s~Sig
    c.sig

# Checking commands one after another is checking the first ones, then the
# rest after them.
lemma check_append sig xs ys : sig~Sig, xs~List Command, ys~List Command, check_all sig xs == Ok ()
    ensures check_all sig (xs ++ ys) == check_all (extend_all sig xs) ys
    proof
        match xs
            []        -> auto
            x :: rest ->
                have check_command sig x == Ok ()
                have check_append (extend sig x) rest ys

lemma extend_append sig xs ys : sig~Sig, xs~List Command, ys~List Command
    ensures extend_all sig (xs ++ ys) == extend_all (extend_all sig xs) ys
    proof
        match xs
            []        -> auto
            x :: rest -> have extend_append (extend sig x) rest ys

# `c` with `cmd` after its commands, if `cmd` is well-formed there.
# Appending copies the commands, so `context` of n commands takes time
# quadratic in n; `prepare` (#86) will want better.
export fn add c cmd -> r : c~Context, cmd~Command, r~Result Context Problem, added c cmd r
    let _ = try check_command c.sig cmd
    have check_append empty_sig c.commands [cmd]
    have extend_append empty_sig c.commands [cmd]
    Ok (Context (c.commands ++ [cmd]) (extend c.sig cmd))

# Whether `r` is `c` with `cmd` after its commands, if it is a context.
export transparent fn added c cmd r -> b : c~Context, cmd~Command, r~Result Context Problem, b~Bool
    match r
        Ok d  -> commands d == commands c ++ [cmd]
        Err _ -> True

# The context of `cmds`, if each is well-formed after those before it.
export fn context cmds -> r : cmds~List Command, r~Result Context Problem
    add_all empty cmds

fn add_all c cmds -> r : c~Context, cmds~List Command, r~Result Context Problem
    match cmds
        []          -> Ok c
        cmd :: rest ->
            let d = try add c cmd
            add_all d rest

# ── Facts ────────────────────────────────────────────────────────────────────

# Whether `t` can be a fact of `c`: a `Bool` without free variables.
export fn fact_ok c t -> r : c~Context, t~Term, r~Bool
    check_term c.sig [] t Bool == Ok ()

# Whether `t` can be a fact of `c`, and if not, why.
export fn check_fact c t -> r : c~Context, t~Term, r~Result Unit Problem, (r == Ok ()) == fact_ok c t
    check_term c.sig [] t Bool

# Whether each of `ts` can be a fact of `c`.
export fn facts_ok c ts -> r : c~Context, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> fact_ok c t and facts_ok c rest

# Whether each of `ts` is a term of `c` without free variables.
export fn terms_ok c ts -> r : c~Context, ts~List Term, r~Bool
    match sorts_of c.sig [] ts
        Ok _  -> True
        Err _ -> False

# Whether each of `ts` is a term of `c` without free variables, and if
# not, why.
export fn check_terms c ts -> r : c~Context, ts~List Term, r~Result Unit Problem, (r == Ok ()) == terms_ok c ts
    match sorts_of c.sig [] ts
        Ok _  -> Ok ()
        Err p -> Err p

fn asserts ts -> cs : ts~List Term, cs~List Command
    match ts
        []        -> []
        t :: rest -> Assert t :: asserts rest

lemma asserts_ok c ts : c~Context, ts~List Term, facts_ok c ts
    ensures check_all c.sig (asserts ts) == Ok () and extend_all c.sig (asserts ts) == c.sig
    proof
        match ts
            []        -> auto
            _ :: rest -> have asserts_ok c rest

# `c` with the facts `ts` added after its commands.
export fn with_facts c ts -> r : c~Context, ts~List Term, facts_ok c ts, r~Context
    have asserts_ok c ts
    have check_append empty_sig c.commands (asserts ts)
    have extend_append empty_sig c.commands (asserts ts)
    Context (c.commands ++ asserts ts) c.sig

# The ground facts, in order.
export fn facts c -> ts : c~Context, ts~List Term
    facts_in c.commands

fn facts_in cs -> ts : cs~List Command, ts~List Term
    match cs
        []               -> []
        Assert t :: rest -> t :: facts_in rest
        _ :: rest        -> facts_in rest

# The axioms, in order.
export fn axioms c -> r : c~Context, r~List Axiom
    axioms_in c.commands

fn axioms_in cs -> r : cs~List Command, r~List Axiom
    match cs
        []               -> []
        Assume a :: rest -> a :: axioms_in rest
        _ :: rest        -> axioms_in rest

# The recursive definitions, in order, each with its function's number.
export fn defs c -> r : c~Context, r~List (Nat, Def)
    defs_in 0 c.commands

fn defs_in n cs -> r : n~Nat, cs~List Command, r~List (Nat, Def)
    match cs
        []                      -> []
        DeclareFun _ :: rest    -> defs_in (n + 1) rest
        DefineFuns _ ds :: rest -> numbered n ds ++ defs_in (n + list.length ds) rest
        _ :: rest               -> defs_in n rest

fn numbered n ds -> r : n~Nat, ds~List Def, r~List (Nat, Def)
    match ds
        []        -> []
        d :: rest -> (n, d) :: numbered (n + 1) rest

# ── Weakening ────────────────────────────────────────────────────────────────

# `sig` with more declarations after its own.
fn grow sig a b c w -> r : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness, r~Sig
    Sig (sig.sorts ++ a) (sig.datatypes ++ b) (sig.funs ++ c) (sig.values ++ w)

lemma sort_ok_grow sig a b c w np s : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness, np~Nat, s~Sort,
                                      sort_ok sig np s
    ensures sort_ok (grow sig a b c w) np s
    proof
        match s
            Seq e       -> have sort_ok_grow sig a b c w np e
            Arr i v     ->
                have sort_ok_grow sig a b c w np i
                have sort_ok_grow sig a b c w np v
            Data _ args -> have sorts_ok_grow sig a b c w np args
            Unin _ args -> have sorts_ok_grow sig a b c w np args
            _           -> auto

lemma sorts_ok_grow sig a b c w np ss : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness, np~Nat,
                                        ss~List Sort, sorts_ok sig np ss
    ensures sorts_ok (grow sig a b c w) np ss
    proof
        match ss
            []        -> auto
            s :: rest ->
                have sort_ok_grow sig a b c w np s
                have sorts_ok_grow sig a b c w np rest

lemma ctor_grow sig a b c w d k : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness, d~Nat, k~Nat,
                                  ctor sig d k != None
    ensures ctor (grow sig a b c w) d k == ctor sig d k
    proof
        auto

lemma apply_grow sig a b c w h found s : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness, h~Head,
                                         found~List Sort, s~Sort, apply_sort sig h found == Ok s
    ensures apply_sort (grow sig a b c w) h found == Ok s
    proof
        match h
            Con d k args ->
                have ctor_grow sig a b c w d k
                have sort_ok_grow sig a b c w 0 (Data d args)
            Is d k       -> have ctor_grow sig a b c w d k
            Sel d k _    -> have ctor_grow sig a b c w d k
            ConstArr t   -> have sort_ok_grow sig a b c w 0 t
            EmptySeq t   -> have sort_ok_grow sig a b c w 0 t
            _            -> auto

lemma sort_of_grow sig a b c w env t s : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness,
                                         env~List Sort, t~Term, s~Sort, sort_of sig env t == Ok s
    ensures sort_of (grow sig a b c w) env t == Ok s
    proof
        match t
            Var _          -> auto
            App h args     ->
                match sorts_of sig env args
                    Ok found ->
                        have sorts_of_grow sig a b c w env args found
                        have apply_grow sig a b c w h found s
                    Err _    -> auto
            Let binds body ->
                match bound_sorts sig env binds
                    Ok ss ->
                        have bound_grow sig a b c w env binds ss
                        have sort_of_grow sig a b c w (list.reverse ss ++ env) body s
                    Err _ -> auto
            Lam _ v body   ->
                have sort_ok_grow sig a b c w 0 v
                match sort_of sig (v :: env) body
                    Ok bs -> have sort_of_grow sig a b c w (v :: env) body bs
                    Err _ -> auto

lemma sorts_of_grow sig a b c w env ts ss : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness,
                                            env~List Sort, ts~List Term, ss~List Sort, sorts_of sig env ts == Ok ss
    ensures sorts_of (grow sig a b c w) env ts == Ok ss
    proof
        match ts
            []        -> auto
            t :: rest ->
                match (sort_of sig env t, sorts_of sig env rest)
                    (Ok s, Ok more) ->
                        have sort_of_grow sig a b c w env t s
                        have sorts_of_grow sig a b c w env rest more
                    _               -> auto

lemma bound_grow sig a b c w env bs ss : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness,
                                         env~List Sort, bs~List (Name, Term), ss~List Sort, bound_sorts sig env bs == Ok ss
    ensures bound_sorts (grow sig a b c w) env bs == Ok ss
    proof
        match bs
            []             -> auto
            (_, t) :: rest ->
                match (sort_of sig env t, bound_sorts sig env rest)
                    (Ok s, Ok more) ->
                        have sort_of_grow sig a b c w env t s
                        have bound_grow sig a b c w env rest more
                    _               -> auto

# A term keeps its sort when a command declares more.
lemma sort_of_extend sig cmd env t s : sig~Sig, cmd~Command, env~List Sort, t~Term, s~Sort, sort_of sig env t == Ok s
    ensures sort_of (extend sig cmd) env t == Ok s
    proof
        let no_sorts = array.from_list []
        let no_dts = array.from_list []
        let no_funs = array.from_list []
        let no_vals = array.from_list []
        have sig.sorts ++ no_sorts == sig.sorts
        have sig.datatypes ++ no_dts == sig.datatypes
        have sig.funs ++ no_funs == sig.funs
        have sig.values ++ no_vals == sig.values
        match cmd
            DeclareSort d       ->
                have extend sig cmd == grow sig (array.from_list [d]) no_dts no_funs no_vals
                have sort_of_grow sig (array.from_list [d]) no_dts no_funs no_vals env t s
            DeclareDatatypes ds ->
                have extend sig cmd == grow sig no_sorts (array.from_list ds) no_funs (array.from_list (group_values sig ds))
                have sort_of_grow sig no_sorts (array.from_list ds) no_funs (array.from_list (group_values sig ds)) env t s
            DeclareFun f        ->
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list [f]) no_vals
                have sort_of_grow sig no_sorts no_dts (array.from_list [f]) no_vals env t s
            DefineFuns _ ds     ->
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list (def_funs ds)) no_vals
                have sort_of_grow sig no_sorts no_dts (array.from_list (def_funs ds)) no_vals env t s
            _                   -> auto

# A term keeps its sort when commands declare more.
lemma sort_of_extend_all sig cmds env t s : sig~Sig, cmds~List Command, env~List Sort, t~Term, s~Sort,
                                            sort_of sig env t == Ok s
    ensures sort_of (extend_all sig cmds) env t == Ok s
    proof
        match cmds
            []          -> auto
            cmd :: rest ->
                have sort_of_extend sig cmd env t s
                have sort_of_extend_all (extend sig cmd) rest env t s

# Whether each of `ts` is a fact in `sig`.
fn facts_in_sig sig ts -> r : sig~Sig, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> check_term sig [] t Bool == Ok () and facts_in_sig sig rest

lemma facts_checked sig cmds : sig~Sig, cmds~List Command, check_all sig cmds == Ok ()
    ensures facts_in_sig (extend_all sig cmds) (facts_in cmds)
    proof
        match cmds
            []          -> auto
            cmd :: rest ->
                have check_command sig cmd == Ok ()
                have facts_checked (extend sig cmd) rest
                match cmd
                    Assert t -> have sort_of_extend_all sig rest [] t Bool
                    _        -> auto

lemma facts_ok_sig c ts : c~Context, ts~List Term, facts_in_sig c.sig ts
    ensures facts_ok c ts
    proof
        match ts
            []        -> auto
            _ :: rest -> have facts_ok_sig c rest

# Every fact of a context is a `Bool` without free variables in it.
export lemma facts_well_sorted c : c~Context
    ensures facts_ok c (facts c)
    proof
        have facts_checked empty_sig c.commands
        have facts_ok_sig c (facts c)

# Whether `a`'s body is a `Bool` in `c`, its variables bound.
export fn axiom_ok c a -> r : c~Context, a~Axiom, r~Bool
    check_term c.sig (binder_env a.vars) a.body Bool == Ok ()

# Whether each of `as` is an axiom of `c` in that sense.
export fn axioms_ok c xs -> r : c~Context, xs~List Axiom, r~Bool
    match xs
        []        -> True
        a :: rest -> axiom_ok c a and axioms_ok c rest

fn axioms_in_sig sig xs -> r : sig~Sig, xs~List Axiom, r~Bool
    match xs
        []        -> True
        a :: rest -> check_term sig (binder_env a.vars) a.body Bool == Ok () and axioms_in_sig sig rest

lemma axioms_checked sig cmds : sig~Sig, cmds~List Command, check_all sig cmds == Ok ()
    ensures axioms_in_sig (extend_all sig cmds) (axioms_in cmds)
    proof
        match cmds
            []          -> auto
            cmd :: rest ->
                have check_command sig cmd == Ok ()
                have axioms_checked (extend sig cmd) rest
                match cmd
                    Assume a ->
                        have check_sorts sig 0 (var_sorts a.vars) == Ok ()
                        have check_term sig (binder_env a.vars) a.body Bool == Ok ()
                        have sort_of_extend_all sig rest (binder_env a.vars) a.body Bool
                    _        -> auto

lemma axioms_ok_sig c xs : c~Context, xs~List Axiom, axioms_in_sig c.sig xs
    ensures axioms_ok c xs
    proof
        match xs
            []        -> auto
            _ :: rest -> have axioms_ok_sig c rest

# Every axiom of a context has a `Bool` body in it.
export lemma axioms_well_sorted c : c~Context
    ensures axioms_ok c (axioms c)
    proof
        have axioms_checked empty_sig c.commands
        have axioms_ok_sig c (axioms c)

# ── What writing a context needs ─────────────────────────────────────────────
# Every number in a well-formed context names a declaration, and every
# variable a binder around it, so its name can be written. These say so
# without sorts: `heads_ok` checks the heads and sorts of a term, `scoped`
# its variables.

# Whether every variable of `t` is bound, with `n` variables bound around it.
export transparent fn scoped n t -> r : n~Nat, t~Term, r~Bool
    match t
        Var i          -> i < n
        App _ args     -> all_scoped n args
        Let binds body -> binds_scoped n binds and scoped (n + list.length binds) body
        Lam _ _ body   -> scoped (n + 1) body

export transparent fn all_scoped n ts -> r : n~Nat, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> scoped n t and all_scoped n rest

export transparent fn binds_scoped n bs -> r : n~Nat, bs~List (Name, Term), r~Bool
    match bs
        []             -> True
        (_, t) :: rest -> scoped n t and binds_scoped n rest

export transparent fn patterns_scoped n ps -> r : n~Nat, ps~List (List Term), r~Bool
    match ps
        []        -> True
        p :: rest -> all_scoped n p and patterns_scoped n rest

# Whether `h`'s numbers name declarations of `sig`, and its sorts are sorts.
export transparent fn head_ok sig h -> r : sig~Sig, h~Head, r~Bool
    match h
        Fun f        -> f < len sig.funs
        Con d k args -> ctor sig d k != None and sort_ok sig 0 (Data d args)
        Is d k       -> ctor sig d k != None
        Sel d k j    ->
            match ctor sig d k
                Some c -> list.head (list.drop j c.fields) != None
                None   -> False
        ConstArr s   -> sort_ok sig 0 s
        EmptySeq s   -> sort_ok sig 0 s
        _            -> True

# Whether every head of `t` is `head_ok`, and every `lambda`'s sort a sort.
export transparent fn heads_ok sig t -> r : sig~Sig, t~Term, r~Bool
    match t
        Var _          -> True
        App h args     -> head_ok sig h and all_heads_ok sig args
        Let binds body -> binds_heads_ok sig binds and heads_ok sig body
        Lam _ s body   -> sort_ok sig 0 s and heads_ok sig body

export transparent fn all_heads_ok sig ts -> r : sig~Sig, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> heads_ok sig t and all_heads_ok sig rest

export transparent fn binds_heads_ok sig bs -> r : sig~Sig, bs~List (Name, Term), r~Bool
    match bs
        []             -> True
        (_, t) :: rest -> heads_ok sig t and binds_heads_ok sig rest

export transparent fn patterns_heads_ok sig ps -> r : sig~Sig, ps~List (List Term), r~Bool
    match ps
        []        -> True
        p :: rest -> all_heads_ok sig p and patterns_heads_ok sig rest

export transparent fn ctors_ok sig np cs -> r : sig~Sig, np~Nat, cs~List Ctor, r~Bool
    match cs
        []        -> True
        c :: rest -> sorts_ok sig np (field_sorts c.fields) and ctors_ok sig np rest

export transparent fn datatypes_ok sig ds -> r : sig~Sig, ds~List Datatype, r~Bool
    match ds
        []        -> True
        d :: rest -> ctors_ok sig (list.length d.params) d.ctors and datatypes_ok sig rest

export transparent fn defs_ok sig ds -> r : sig~Sig, ds~List Def, r~Bool
    match ds
        []        -> True
        d :: rest ->
            sorts_ok sig 0 (var_sorts d.params) and sort_ok sig 0 d.result and heads_ok sig d.body
                and scoped (list.length d.params) d.body and defs_ok sig rest

# Whether everything `cmd` names is declared in `sig`.
export transparent fn command_ok sig cmd -> r : sig~Sig, cmd~Command, r~Bool
    match cmd
        DeclareSort _       -> True
        DeclareDatatypes ds -> datatypes_ok sig ds
        DeclareFun f        -> sorts_ok sig 0 f.params and sort_ok sig 0 f.result
        DefineFuns _ ds     -> defs_ok sig ds
        Assume a            ->
            sorts_ok sig 0 (var_sorts a.vars) and heads_ok sig a.body and patterns_heads_ok sig a.patterns
                and scoped (list.length a.vars) a.body and patterns_scoped (list.length a.vars) a.patterns
        Assert t            -> heads_ok sig t and scoped 0 t

export transparent fn commands_ok sig cmds -> r : sig~Sig, cmds~List Command, r~Bool
    match cmds
        []        -> True
        c :: rest -> command_ok sig c and commands_ok sig rest

lemma apply_heads sig h found s : sig~Sig, h~Head, found~List Sort, s~Sort, apply_sort sig h found == Ok s
    ensures head_ok sig h
    proof
        auto

lemma sort_of_heads sig env t s : sig~Sig, env~List Sort, t~Term, s~Sort, sort_of sig env t == Ok s
    ensures heads_ok sig t
    proof
        match t
            Var _          -> auto
            App h args     ->
                match sorts_of sig env args
                    Ok found ->
                        have sorts_of_heads sig env args found
                        have apply_heads sig h found s
                    Err _    -> auto
            Let binds body ->
                match bound_sorts sig env binds
                    Ok ss ->
                        have bound_heads sig env binds ss
                        have sort_of_heads sig (list.reverse ss ++ env) body s
                    Err _ -> auto
            Lam _ v body   ->
                match sort_of sig (v :: env) body
                    Ok b  -> have sort_of_heads sig (v :: env) body b
                    Err _ -> auto

lemma sorts_of_heads sig env ts ss : sig~Sig, env~List Sort, ts~List Term, ss~List Sort, sorts_of sig env ts == Ok ss
    ensures all_heads_ok sig ts
    proof
        match ts
            []        -> auto
            t :: rest ->
                match (sort_of sig env t, sorts_of sig env rest)
                    (Ok s, Ok more) ->
                        have sort_of_heads sig env t s
                        have sorts_of_heads sig env rest more
                    _               -> auto

lemma bound_heads sig env bs ss : sig~Sig, env~List Sort, bs~List (Name, Term), ss~List Sort,
                                  bound_sorts sig env bs == Ok ss
    ensures binds_heads_ok sig bs
    proof
        match bs
            []             -> auto
            (_, t) :: rest ->
                match (sort_of sig env t, bound_sorts sig env rest)
                    (Ok s, Ok more) ->
                        have sort_of_heads sig env t s
                        have bound_heads sig env rest more
                    _               -> auto

# A variable's sort is found only for an index below the environment's length.
lemma drop_head i xs : i~Nat, xs~List a, list.head (list.drop i xs) != None
    ensures i < list.length xs
    proof
        auto

lemma sort_of_scoped sig env t s : sig~Sig, env~List Sort, t~Term, s~Sort, sort_of sig env t == Ok s
    ensures scoped (list.length env) t
    proof
        match t
            Var i          -> have drop_head i env
            App _ args     ->
                match sorts_of sig env args
                    Ok found -> have sorts_of_scoped sig env args found
                    Err _    -> auto
            Let binds body ->
                match bound_sorts sig env binds
                    Ok ss ->
                        have bound_scoped sig env binds ss
                        have list.length_reverse ss
                        have list.length_append (list.reverse ss) env
                        have sort_of_scoped sig (list.reverse ss ++ env) body s
                    Err _ -> auto
            Lam _ v body   ->
                match sort_of sig (v :: env) body
                    Ok b  -> have sort_of_scoped sig (v :: env) body b
                    Err _ -> auto

lemma sorts_of_scoped sig env ts ss : sig~Sig, env~List Sort, ts~List Term, ss~List Sort, sorts_of sig env ts == Ok ss
    ensures all_scoped (list.length env) ts
    proof
        match ts
            []        -> auto
            t :: rest ->
                match (sort_of sig env t, sorts_of sig env rest)
                    (Ok s, Ok more) ->
                        have sort_of_scoped sig env t s
                        have sorts_of_scoped sig env rest more
                    _               -> auto

lemma bound_scoped sig env bs ss : sig~Sig, env~List Sort, bs~List (Name, Term), ss~List Sort,
                                   bound_sorts sig env bs == Ok ss
    ensures binds_scoped (list.length env) bs and list.length ss == list.length bs
    proof
        match bs
            []             -> auto
            (_, t) :: rest ->
                match (sort_of sig env t, bound_sorts sig env rest)
                    (Ok s, Ok more) ->
                        have sort_of_scoped sig env t s
                        have bound_scoped sig env rest more
                    _               -> auto

lemma check_term_scoped sig env t want : sig~Sig, env~List Sort, t~Term, want~Sort, check_term sig env t want == Ok ()
    ensures scoped (list.length env) t
    proof
        match sort_of sig env t
            Ok s  -> have sort_of_scoped sig env t s
            Err _ -> auto

lemma check_patterns_scoped sig env ps : sig~Sig, env~List Sort, ps~List (List Term),
                                         check_patterns sig env ps == Ok ()
    ensures patterns_scoped (list.length env) ps
    proof
        match ps
            []        -> auto
            p :: rest ->
                match sorts_of sig env p
                    Ok ss ->
                        have sorts_of_scoped sig env p ss
                        have check_patterns_scoped sig env rest
                    Err _ -> auto

# A binder list's body has a variable for each binder.
lemma binder_env_length vs : vs~List (Name, Sort)
    ensures list.length (binder_env vs) == list.length vs
    proof
        have var_sorts_length vs
        have list.length_reverse (var_sorts vs)

lemma var_sorts_length vs : vs~List (Name, Sort)
    ensures list.length (var_sorts vs) == list.length vs
    proof
        match vs
            []        -> auto
            _ :: rest -> have var_sorts_length rest

lemma head_grow sig a b c w h : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness, h~Head, head_ok sig h
    ensures head_ok (grow sig a b c w) h
    proof
        match h
            Con d k args ->
                have ctor_grow sig a b c w d k
                have sort_ok_grow sig a b c w 0 (Data d args)
            Is d k       -> have ctor_grow sig a b c w d k
            Sel d k _    -> have ctor_grow sig a b c w d k
            ConstArr t   -> have sort_ok_grow sig a b c w 0 t
            EmptySeq t   -> have sort_ok_grow sig a b c w 0 t
            _            -> auto

lemma heads_grow sig a b c w t : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness, t~Term, heads_ok sig t
    ensures heads_ok (grow sig a b c w) t
    proof
        match t
            Var _          -> auto
            App h args     ->
                have head_grow sig a b c w h
                have all_heads_grow sig a b c w args
            Let binds body ->
                have binds_heads_grow sig a b c w binds
                have heads_grow sig a b c w body
            Lam _ v body   ->
                have sort_ok_grow sig a b c w 0 v
                have heads_grow sig a b c w body

lemma all_heads_grow sig a b c w ts : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness, ts~List Term,
                                      all_heads_ok sig ts
    ensures all_heads_ok (grow sig a b c w) ts
    proof
        match ts
            []        -> auto
            t :: rest ->
                have heads_grow sig a b c w t
                have all_heads_grow sig a b c w rest

lemma binds_heads_grow sig a b c w bs : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness,
                                        bs~List (Name, Term), binds_heads_ok sig bs
    ensures binds_heads_ok (grow sig a b c w) bs
    proof
        match bs
            []             -> auto
            (_, t) :: rest ->
                have heads_grow sig a b c w t
                have binds_heads_grow sig a b c w rest

lemma patterns_heads_grow sig a b c w ps : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness,
                                           ps~List (List Term), patterns_heads_ok sig ps
    ensures patterns_heads_ok (grow sig a b c w) ps
    proof
        match ps
            []        -> auto
            p :: rest ->
                have all_heads_grow sig a b c w p
                have patterns_heads_grow sig a b c w rest

lemma ctors_grow sig a b c w np cs : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness, np~Nat,
                                     cs~List Ctor, ctors_ok sig np cs
    ensures ctors_ok (grow sig a b c w) np cs
    proof
        match cs
            []        -> auto
            k :: rest ->
                have sorts_ok_grow sig a b c w np (field_sorts k.fields)
                have ctors_grow sig a b c w np rest

lemma datatypes_grow sig a b c w ds : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness,
                                      ds~List Datatype, datatypes_ok sig ds
    ensures datatypes_ok (grow sig a b c w) ds
    proof
        match ds
            []        -> auto
            d :: rest ->
                have ctors_grow sig a b c w (list.length d.params) d.ctors
                have datatypes_grow sig a b c w rest

lemma defs_grow sig a b c w ds : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness, ds~List Def,
                                 defs_ok sig ds
    ensures defs_ok (grow sig a b c w) ds
    proof
        match ds
            []        -> auto
            d :: rest ->
                have sorts_ok_grow sig a b c w 0 (var_sorts d.params)
                have sort_ok_grow sig a b c w 0 d.result
                have heads_grow sig a b c w d.body
                have defs_grow sig a b c w rest

lemma command_grow sig a b c w cmd : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness, cmd~Command,
                                     command_ok sig cmd
    ensures command_ok (grow sig a b c w) cmd
    proof
        match cmd
            DeclareSort _       -> auto
            DeclareDatatypes ds -> have datatypes_grow sig a b c w ds
            DeclareFun f        ->
                have sorts_ok_grow sig a b c w 0 f.params
                have sort_ok_grow sig a b c w 0 f.result
            DefineFuns _ ds     -> have defs_grow sig a b c w ds
            Assume x            ->
                have sorts_ok_grow sig a b c w 0 (var_sorts x.vars)
                have heads_grow sig a b c w x.body
                have patterns_heads_grow sig a b c w x.patterns
            Assert t            -> have heads_grow sig a b c w t

lemma command_extend sig cmd x : sig~Sig, cmd~Command, x~Command, command_ok sig x
    ensures command_ok (extend sig cmd) x
    proof
        let no_sorts = array.from_list []
        let no_dts = array.from_list []
        let no_funs = array.from_list []
        let no_vals = array.from_list []
        have sig.sorts ++ no_sorts == sig.sorts
        have sig.datatypes ++ no_dts == sig.datatypes
        have sig.funs ++ no_funs == sig.funs
        have sig.values ++ no_vals == sig.values
        match cmd
            DeclareSort d       ->
                have extend sig cmd == grow sig (array.from_list [d]) no_dts no_funs no_vals
                have command_grow sig (array.from_list [d]) no_dts no_funs no_vals x
            DeclareDatatypes ds ->
                have extend sig cmd == grow sig no_sorts (array.from_list ds) no_funs (array.from_list (group_values sig ds))
                have command_grow sig no_sorts (array.from_list ds) no_funs (array.from_list (group_values sig ds)) x
            DeclareFun f        ->
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list [f]) no_vals
                have command_grow sig no_sorts no_dts (array.from_list [f]) no_vals x
            DefineFuns _ ds     ->
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list (def_funs ds)) no_vals
                have command_grow sig no_sorts no_dts (array.from_list (def_funs ds)) no_vals x
            _                   -> auto

lemma command_extend_all sig cmds x : sig~Sig, cmds~List Command, x~Command, command_ok sig x
    ensures command_ok (extend_all sig cmds) x
    proof
        match cmds
            []          -> auto
            cmd :: rest ->
                have command_extend sig cmd x
                have command_extend_all (extend sig cmd) rest x

lemma check_sorts_ok sig np ss : sig~Sig, np~Nat, ss~List Sort, check_sorts sig np ss == Ok ()
    ensures sorts_ok sig np ss
    proof
        match ss
            []        -> auto
            _ :: rest -> have check_sorts_ok sig np rest

lemma check_term_heads sig env t want : sig~Sig, env~List Sort, t~Term, want~Sort, check_term sig env t want == Ok ()
    ensures heads_ok sig t
    proof
        match sort_of sig env t
            Ok s  -> have sort_of_heads sig env t s
            Err _ -> auto

lemma check_ctors_ok sig np cs : sig~Sig, np~Nat, cs~List Ctor, check_ctors sig np cs == Ok ()
    ensures ctors_ok sig np cs
    proof
        match cs
            []        -> auto
            k :: rest ->
                have check_sorts_ok sig np (field_sorts k.fields)
                have check_ctors_ok sig np rest

lemma check_datatypes_ok sig ds : sig~Sig, ds~List Datatype, check_datatypes sig ds == Ok ()
    ensures datatypes_ok sig ds
    proof
        match ds
            []        -> auto
            d :: rest ->
                have check_ctors_ok sig (list.length d.params) d.ctors
                have check_datatypes_ok sig rest

# `defs_ok` for definitions whose signatures were checked in `sig` and
# bodies in `big`, which `sig` grows into.
lemma check_defs_ok sig big a b c w ds : sig~Sig, big~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, w~Array Witness,
                                         big == grow sig a b c w, ds~List Def,
                                         check_sigs sig ds == Ok (), check_bodies big ds == Ok ()
    ensures defs_ok big ds
    proof
        match ds
            []        -> auto
            d :: rest ->
                have check_sorts_ok sig 0 (var_sorts d.params)
                have sorts_ok_grow sig a b c w 0 (var_sorts d.params)
                have check_sort sig 0 d.result == Ok ()
                have sort_ok_grow sig a b c w 0 d.result
                have check_term_heads big (binder_env d.params) d.body d.result
                have check_term_scoped big (binder_env d.params) d.body d.result
                have binder_env_length d.params
                have check_defs_ok sig big a b c w rest

lemma check_patterns_ok sig env ps : sig~Sig, env~List Sort, ps~List (List Term), check_patterns sig env ps == Ok ()
    ensures patterns_heads_ok sig ps
    proof
        match ps
            []        -> auto
            p :: rest ->
                match sorts_of sig env p
                    Ok ss ->
                        have sorts_of_heads sig env p ss
                        have check_patterns_ok sig env rest
                    Err _ -> auto

lemma checked_command_ok sig cmd : sig~Sig, cmd~Command, check_command sig cmd == Ok ()
    ensures command_ok (extend sig cmd) cmd
    proof
        let no_sorts = array.from_list []
        let no_dts = array.from_list []
        let no_funs = array.from_list []
        let no_vals = array.from_list []
        have sig.sorts ++ no_sorts == sig.sorts
        have sig.datatypes ++ no_dts == sig.datatypes
        match cmd
            DeclareSort _       -> auto
            DeclareDatatypes ds -> have check_datatypes_ok (extend sig cmd) ds
            DeclareFun f        ->
                have check_sorts_ok sig 0 f.params
                have check_sort sig 0 f.result == Ok ()
                have command_extend sig cmd cmd
                have sorts_ok sig 0 f.params
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list [f]) no_vals
                have sorts_ok_grow sig no_sorts no_dts (array.from_list [f]) no_vals 0 f.params
                have sort_ok_grow sig no_sorts no_dts (array.from_list [f]) no_vals 0 f.result
            DefineFuns _ ds     ->
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list (def_funs ds)) no_vals
                have check_defs_ok sig (extend sig cmd) no_sorts no_dts (array.from_list (def_funs ds)) no_vals ds
            Assume x            ->
                have check_sorts_ok sig 0 (var_sorts x.vars)
                have check_term_heads sig (binder_env x.vars) x.body Bool
                have check_patterns_ok sig (binder_env x.vars) x.patterns
                have check_term_scoped sig (binder_env x.vars) x.body Bool
                have check_patterns_scoped sig (binder_env x.vars) x.patterns
                have binder_env_length x.vars
            Assert t            ->
                have check_term_heads sig [] t Bool
                have check_term_scoped sig [] t Bool

lemma checked_commands_ok sig cmds : sig~Sig, cmds~List Command, check_all sig cmds == Ok ()
    ensures commands_ok (extend_all sig cmds) cmds
    proof
        match cmds
            []          -> auto
            cmd :: rest ->
                have check_command sig cmd == Ok ()
                have checked_command_ok sig cmd
                have command_extend_all (extend sig cmd) rest cmd
                have checked_commands_ok (extend sig cmd) rest

# Everything a context's commands name is declared in it.
export lemma commands_well_formed c : c~Context
    ensures commands_ok (signature c) (commands c)
    proof
        have checked_commands_ok empty_sig c.commands

# Every head of a fact is declared in the context, and it has no free
# variables.
export lemma fact_heads c t : c~Context, t~Term, fact_ok c t
    ensures heads_ok (signature c) t and scoped 0 t
    proof
        have check_term_heads c.sig [] t Bool
        have check_term_scoped c.sig [] t Bool

# Every head of terms of the context is declared in it.
export lemma terms_heads c ts : c~Context, ts~List Term, terms_ok c ts
    ensures all_heads_ok (signature c) ts and all_scoped 0 ts
    proof
        match sorts_of c.sig [] ts
            Ok ss ->
                have sorts_of_heads c.sig [] ts ss
                have sorts_of_scoped c.sig [] ts ss
            Err _ -> auto
