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
# promise that evaluating it terminates (trusted only for counterexamples).
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

# Everything declared so far, numbered in order.
export record Sig
    sorts~Array SortDecl
    datatypes~Array Datatype
    funs~Array FunDecl

export fn empty_sig -> s : s~Sig
    Sig (array.from_list []) (array.from_list []) (array.from_list [])

fn def_fun d -> f : d~Def, f~FunDecl
    FunDecl d.name (list.map (\(_, s) -> s) d.params) d.result Defined

fn def_funs ds -> fs : ds~List Def, fs~List FunDecl
    list.map def_fun ds

# The signature after `c`.
export fn extend sig c -> r : sig~Sig, c~Command, r~Sig
    match c
        DeclareSort d       -> Sig (sig.sorts ++ array.from_list [d]) sig.datatypes sig.funs
        DeclareDatatypes ds -> Sig sig.sorts (sig.datatypes ++ array.from_list ds) sig.funs
        DeclareFun f        -> Sig sig.sorts sig.datatypes (sig.funs ++ array.from_list [f])
        DefineFuns _ ds     -> Sig sig.sorts sig.datatypes (sig.funs ++ array.from_list (def_funs ds))
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

# Whether `c` is well-formed after the commands that gave `sig`.
export fn check_command sig c -> r : sig~Sig, c~Command, r~Result Unit Problem
    match c
        DeclareSort _       -> Ok ()
        DeclareDatatypes ds -> check_datatypes (extend sig c) ds
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
fn grow sig a b c -> r : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, r~Sig
    Sig (sig.sorts ++ a) (sig.datatypes ++ b) (sig.funs ++ c)

lemma sort_ok_grow sig a b c np s : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, np~Nat, s~Sort,
                                    sort_ok sig np s
    ensures sort_ok (grow sig a b c) np s
    proof
        match s
            Seq e       -> have sort_ok_grow sig a b c np e
            Arr i v     ->
                have sort_ok_grow sig a b c np i
                have sort_ok_grow sig a b c np v
            Data _ args -> have sorts_ok_grow sig a b c np args
            Unin _ args -> have sorts_ok_grow sig a b c np args
            _           -> auto

lemma sorts_ok_grow sig a b c np ss : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, np~Nat,
                                      ss~List Sort, sorts_ok sig np ss
    ensures sorts_ok (grow sig a b c) np ss
    proof
        match ss
            []        -> auto
            s :: rest ->
                have sort_ok_grow sig a b c np s
                have sorts_ok_grow sig a b c np rest

lemma ctor_grow sig a b c d k : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, d~Nat, k~Nat,
                                ctor sig d k != None
    ensures ctor (grow sig a b c) d k == ctor sig d k
    proof
        auto

lemma apply_grow sig a b c h found s : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, h~Head,
                                       found~List Sort, s~Sort, apply_sort sig h found == Ok s
    ensures apply_sort (grow sig a b c) h found == Ok s
    proof
        match h
            Con d k args ->
                have ctor_grow sig a b c d k
                have sort_ok_grow sig a b c 0 (Data d args)
            Is d k       -> have ctor_grow sig a b c d k
            Sel d k _    -> have ctor_grow sig a b c d k
            ConstArr t   -> have sort_ok_grow sig a b c 0 t
            EmptySeq t   -> have sort_ok_grow sig a b c 0 t
            _            -> auto

lemma sort_of_grow sig a b c env t s : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl,
                                       env~List Sort, t~Term, s~Sort, sort_of sig env t == Ok s
    ensures sort_of (grow sig a b c) env t == Ok s
    proof
        match t
            Var _          -> auto
            App h args     ->
                match sorts_of sig env args
                    Ok found ->
                        have sorts_of_grow sig a b c env args found
                        have apply_grow sig a b c h found s
                    Err _    -> auto
            Let binds body ->
                match bound_sorts sig env binds
                    Ok ss ->
                        have bound_grow sig a b c env binds ss
                        have sort_of_grow sig a b c (list.reverse ss ++ env) body s
                    Err _ -> auto
            Lam _ v body   ->
                have sort_ok_grow sig a b c 0 v
                match sort_of sig (v :: env) body
                    Ok bs -> have sort_of_grow sig a b c (v :: env) body bs
                    Err _ -> auto

lemma sorts_of_grow sig a b c env ts ss : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl,
                                          env~List Sort, ts~List Term, ss~List Sort, sorts_of sig env ts == Ok ss
    ensures sorts_of (grow sig a b c) env ts == Ok ss
    proof
        match ts
            []        -> auto
            t :: rest ->
                match (sort_of sig env t, sorts_of sig env rest)
                    (Ok s, Ok more) ->
                        have sort_of_grow sig a b c env t s
                        have sorts_of_grow sig a b c env rest more
                    _               -> auto

lemma bound_grow sig a b c env bs ss : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl,
                                       env~List Sort, bs~List (Name, Term), ss~List Sort, bound_sorts sig env bs == Ok ss
    ensures bound_sorts (grow sig a b c) env bs == Ok ss
    proof
        match bs
            []             -> auto
            (_, t) :: rest ->
                match (sort_of sig env t, bound_sorts sig env rest)
                    (Ok s, Ok more) ->
                        have sort_of_grow sig a b c env t s
                        have bound_grow sig a b c env rest more
                    _               -> auto

# A term keeps its sort when a command declares more.
lemma sort_of_extend sig cmd env t s : sig~Sig, cmd~Command, env~List Sort, t~Term, s~Sort, sort_of sig env t == Ok s
    ensures sort_of (extend sig cmd) env t == Ok s
    proof
        let no_sorts = array.from_list []
        let no_dts = array.from_list []
        let no_funs = array.from_list []
        have sig.sorts ++ no_sorts == sig.sorts
        have sig.datatypes ++ no_dts == sig.datatypes
        have sig.funs ++ no_funs == sig.funs
        match cmd
            DeclareSort d       ->
                have extend sig cmd == grow sig (array.from_list [d]) no_dts no_funs
                have sort_of_grow sig (array.from_list [d]) no_dts no_funs env t s
            DeclareDatatypes ds ->
                have extend sig cmd == grow sig no_sorts (array.from_list ds) no_funs
                have sort_of_grow sig no_sorts (array.from_list ds) no_funs env t s
            DeclareFun f        ->
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list [f])
                have sort_of_grow sig no_sorts no_dts (array.from_list [f]) env t s
            DefineFuns _ ds     ->
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list (def_funs ds))
                have sort_of_grow sig no_sorts no_dts (array.from_list (def_funs ds)) env t s
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

lemma head_grow sig a b c h : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, h~Head, head_ok sig h
    ensures head_ok (grow sig a b c) h
    proof
        match h
            Con d k args ->
                have ctor_grow sig a b c d k
                have sort_ok_grow sig a b c 0 (Data d args)
            Is d k       -> have ctor_grow sig a b c d k
            Sel d k _    -> have ctor_grow sig a b c d k
            ConstArr t   -> have sort_ok_grow sig a b c 0 t
            EmptySeq t   -> have sort_ok_grow sig a b c 0 t
            _            -> auto

lemma heads_grow sig a b c t : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, t~Term, heads_ok sig t
    ensures heads_ok (grow sig a b c) t
    proof
        match t
            Var _          -> auto
            App h args     ->
                have head_grow sig a b c h
                have all_heads_grow sig a b c args
            Let binds body ->
                have binds_heads_grow sig a b c binds
                have heads_grow sig a b c body
            Lam _ v body   ->
                have sort_ok_grow sig a b c 0 v
                have heads_grow sig a b c body

lemma all_heads_grow sig a b c ts : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, ts~List Term,
                                    all_heads_ok sig ts
    ensures all_heads_ok (grow sig a b c) ts
    proof
        match ts
            []        -> auto
            t :: rest ->
                have heads_grow sig a b c t
                have all_heads_grow sig a b c rest

lemma binds_heads_grow sig a b c bs : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl,
                                      bs~List (Name, Term), binds_heads_ok sig bs
    ensures binds_heads_ok (grow sig a b c) bs
    proof
        match bs
            []             -> auto
            (_, t) :: rest ->
                have heads_grow sig a b c t
                have binds_heads_grow sig a b c rest

lemma patterns_heads_grow sig a b c ps : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl,
                                         ps~List (List Term), patterns_heads_ok sig ps
    ensures patterns_heads_ok (grow sig a b c) ps
    proof
        match ps
            []        -> auto
            p :: rest ->
                have all_heads_grow sig a b c p
                have patterns_heads_grow sig a b c rest

lemma ctors_grow sig a b c np cs : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, np~Nat,
                                   cs~List Ctor, ctors_ok sig np cs
    ensures ctors_ok (grow sig a b c) np cs
    proof
        match cs
            []        -> auto
            k :: rest ->
                have sorts_ok_grow sig a b c np (field_sorts k.fields)
                have ctors_grow sig a b c np rest

lemma datatypes_grow sig a b c ds : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl,
                                    ds~List Datatype, datatypes_ok sig ds
    ensures datatypes_ok (grow sig a b c) ds
    proof
        match ds
            []        -> auto
            d :: rest ->
                have ctors_grow sig a b c (list.length d.params) d.ctors
                have datatypes_grow sig a b c rest

lemma defs_grow sig a b c ds : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, ds~List Def,
                               defs_ok sig ds
    ensures defs_ok (grow sig a b c) ds
    proof
        match ds
            []        -> auto
            d :: rest ->
                have sorts_ok_grow sig a b c 0 (var_sorts d.params)
                have sort_ok_grow sig a b c 0 d.result
                have heads_grow sig a b c d.body
                have defs_grow sig a b c rest

lemma command_grow sig a b c cmd : sig~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl, cmd~Command,
                                   command_ok sig cmd
    ensures command_ok (grow sig a b c) cmd
    proof
        match cmd
            DeclareSort _       -> auto
            DeclareDatatypes ds -> have datatypes_grow sig a b c ds
            DeclareFun f        ->
                have sorts_ok_grow sig a b c 0 f.params
                have sort_ok_grow sig a b c 0 f.result
            DefineFuns _ ds     -> have defs_grow sig a b c ds
            Assume x            ->
                have sorts_ok_grow sig a b c 0 (var_sorts x.vars)
                have heads_grow sig a b c x.body
                have patterns_heads_grow sig a b c x.patterns
            Assert t            -> have heads_grow sig a b c t

lemma command_extend sig cmd x : sig~Sig, cmd~Command, x~Command, command_ok sig x
    ensures command_ok (extend sig cmd) x
    proof
        let no_sorts = array.from_list []
        let no_dts = array.from_list []
        let no_funs = array.from_list []
        have sig.sorts ++ no_sorts == sig.sorts
        have sig.datatypes ++ no_dts == sig.datatypes
        have sig.funs ++ no_funs == sig.funs
        match cmd
            DeclareSort d       ->
                have extend sig cmd == grow sig (array.from_list [d]) no_dts no_funs
                have command_grow sig (array.from_list [d]) no_dts no_funs x
            DeclareDatatypes ds ->
                have extend sig cmd == grow sig no_sorts (array.from_list ds) no_funs
                have command_grow sig no_sorts (array.from_list ds) no_funs x
            DeclareFun f        ->
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list [f])
                have command_grow sig no_sorts no_dts (array.from_list [f]) x
            DefineFuns _ ds     ->
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list (def_funs ds))
                have command_grow sig no_sorts no_dts (array.from_list (def_funs ds)) x
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
lemma check_defs_ok sig big a b c ds : sig~Sig, big~Sig, a~Array SortDecl, b~Array Datatype, c~Array FunDecl,
                                       big == grow sig a b c, ds~List Def,
                                       check_sigs sig ds == Ok (), check_bodies big ds == Ok ()
    ensures defs_ok big ds
    proof
        match ds
            []        -> auto
            d :: rest ->
                have check_sorts_ok sig 0 (var_sorts d.params)
                have sorts_ok_grow sig a b c 0 (var_sorts d.params)
                have check_sort sig 0 d.result == Ok ()
                have sort_ok_grow sig a b c 0 d.result
                have check_term_heads big (binder_env d.params) d.body d.result
                have check_term_scoped big (binder_env d.params) d.body d.result
                have binder_env_length d.params
                have check_defs_ok sig big a b c rest

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
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list [f])
                have sorts_ok_grow sig no_sorts no_dts (array.from_list [f]) 0 f.params
                have sort_ok_grow sig no_sorts no_dts (array.from_list [f]) 0 f.result
            DefineFuns _ ds     ->
                have extend sig cmd == grow sig no_sorts no_dts (array.from_list (def_funs ds))
                have check_defs_ok sig (extend sig cmd) no_sorts no_dts (array.from_list (def_funs ds)) ds
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
