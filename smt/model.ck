# model.ck — what a term means in a model: `eval`, `holds`, `fails`.
#
# This module is the definition every answer of the solver is checked
# against (#72, design 1). It is written to be read, not to be fast: each
# operation says what it computes, and where SMT-LIB leaves a result
# unspecified, the model says what it is.
#
# **A model is an SMT-LIB structure.** Every sort is a set of elements and
# every symbol a function of them. An uninterpreted sort's elements are
# `Element n`, and an array sort's are `ArrayElem k`, numbers the model
# names (`Model.array_in`), as in SMT-LIB's `ArraysEx`, whose array sorts
# are sets of elements of the structure (2.6, §5.3). The model says what
# every operation that makes an array gives (`const`, `store`, `map +` as
# `sum`, `lambda`) and what `select` reads. Two arrays are equal exactly
# when they are the same element, so equality is decided for every pair of
# values, and a model's function may take arrays. What makes these arrays
# (read over write, extensionality and the rest) is not computed here:
# `arrays_ok` below states it, for a theorem to take as its premise. They
# are `ArraysEx`'s arrays and more: `arrays_total` asks the model to name an
# array for every `lambda` of the context's signature, so every function a
# term defines is an array. `ArraysEx` doesn't ask that (its arrays are any
# set with the laws); `ckc`'s queries do, since a Checkers function value is
# a function and SPEC §7.3 writes it as an array (decided on #85).
#
# **Three answers.** Evaluating a term gives its value, or `Unknown` with a
# reason: the model doesn't say (a partial model, such as the values Z3
# printed), evaluation ran out of fuel (in `refutes`), or the model gave a
# value of the wrong sort. `holds c m t` is true only when `t` evaluates to
# true, and `fails c m t` only when it evaluates to false; when neither,
# nothing is claimed. A definite answer is meant to be the term's value in
# the structure the model describes; that is what S6 proves (`checks_sound`
# and monotonicity, below), and nothing here states it as a lemma.
#
# **Connectives are Kleene's.** `and` is false as soon as one argument is
# false, whatever the others are, and true only if all are true; `or`
# dually; `=>` is `(not a) or b`. This is exact: every term has a value in
# every structure, so a conjunction with a false argument is false whatever
# the unknown arguments' values are. `ite` evaluates its condition, then
# only the branch it chooses. So a definite answer depends only on the
# parts it evaluated: an argument it didn't need may be unknown, or even a
# value of the wrong sort from the model, and the answer stands, because
# it is the same for every value that argument could have. That is the
# monotonicity lemma S6 proves (below).
#
# **Terms of the context only.** `eval` and `eval_unfolding` evaluate a term
# only if it has a sort in the context with no variables free, `holds_at`
# an axiom only if it is well-sorted in the context (`term.axiom_ok`: its
# body a `Bool` with its variables bound; not that it is one of the
# context's axioms), and
# `refutes` a goal only if it is a closed `Bool` term of it
# (`term.fact_ok`); anything else is `IllSorted`, or not held.
#
# **Two modes.** `eval`, `holds`, `fails`, `holds_all` and `holds_at` are the
# meaning: every function, defined ones included, is what `Model.funs` says,
# a `lambda` is the array `Model.lambda` names, and a definition's equation
# is a fact like any other (SMT-LIB defines `define-fun-rec` as a declared
# function and its universally quantified equation). The meaning evaluates
# no body, so it needs no fuel: it goes by the structure of the term, and its
# answers are the same whatever `Model.fuel` is (`eval_fuel` and the lemmas
# beside it).
#
# `refutes`, which `Answer.Invalid` uses, evaluates instead with each
# definition run as its own body (design 3), within `Model.fuel` levels
# (past them, `OutOfFuel`): a `define-fun` (`Plain`) always, and a
# recursive one (`define-fun-rec`, `define-funs-rec`) when marked
# terminating (`Def.terminates`). Only the caller marks a definition:
# `smtlib.parse` marks none, and the package's commands mark every one only
# when given `--terminating`, and then say so. A definition run this way has
# exactly one solution, so its equation holds by construction wherever
# evaluation finishes: a `Plain` one's body applies only functions declared
# before it (`term.plain_bodies`), so it is a function of those; a recursive
# one's, by the mark. `refutes` requires every recursive definition of the
# context to be marked: one that isn't may have no solution at all
# (`g x = g x + 1`), and then no model satisfies the context, whether or not
# an assertion calls it (SMT-LIB 2.6, §4.2.3, note 4). Z3 5.3.3 answers
# `sat` to such a context; this module does not follow it there. Unfolding
# a recursive definition not marked terminating is `NotTerminating`. In the meaning, a model satisfies definition `d` when it
# satisfies `definition_axiom n d` at all values (`holds_at`).
#
# **`refutes` builds its arrays.** It can't take `arrays_ok` on trust, so it
# evaluates in `normal_arrays sig m`: the given model with its arrays
# replaced by normal forms (a constant and the stores that differ from it,
# in order), each array the number `code` gives its normal form. Only those
# numbers are arrays there, so every array `refutes` sees is one, and two
# arrays are meant to be the same element exactly when they are the same
# function (not proved here: S6 owes it, below).
# Every constant array has a normal form; stores have one at `Bool`, at a
# domain the model lists, and at sorts this module can show unbounded
# (`Int`, sequences, a countable domain, arrays of those), not at a
# datatype, which may be finite. A `lambda` has none (`LambdaNotGiven`),
# and nor has an array Z3 prints as a function over a range; `refutes` is
# false for a context or goal with a `lambda` anywhere in it, reached or
# not.
#
# **Quantified axioms.** `holds_at c m a vs` evaluates the body of axiom `a`
# at the values `vs`. A `forall` over an infinite sort can't be evaluated, so
# `refutes` is false for a context with any axiom, patterned or not (an
# `Axiom` with `patterns = []` is a fact like the others, #82): a model is
# never shown to satisfy one, so a query with one is never `Invalid`.
#
# **What S6 proves of this module** (#86; the statements are decided in
# #84, their exact text is S6's, with the certificate format):
#
# - `checks_sound`, in two statements. The first asks the premises (the
#   facts; the axioms and definitions' equations, `holds_at`; `arrays_ok`
#   with `arrays_total` but `lambda`'s; every function of the model total)
#   only at the values of the finite set of terms the certificate uses:
#   every satisfiable context has such a model, so it is never vacuous. The
#   second, a corollary in one step, asks them at all values. Either way the
#   conclusion is that the goal `holds`.
# - Monotonicity: a definite answer in a model is the answer in every model
#   that agrees with it wherever it answers. For a partial model, `not
#   fails` of the goal follows from `holds` by it.
# - The `Invalid` theorem: if `refutes c goal m`, and every recursive
#   definition marked terminating terminates (a named hypothesis: the mark
#   is the caller's word), the interpretation `m` describes, with each
#   definition its unique solution and arrays as `normal_arrays` has them,
#   satisfies every assertion of `c` and `not goal`. A `define-fun` needs
#   no hypothesis: by `term.plain_bodies` its body applies only functions
#   numbered below its own, so by induction on that number it terminates
#   and has one solution once they do.
#
# Together: a query is never both `Valid` and `Invalid`.
#
# Proved so far: both statements (`cert.checks_sound`, and
# `cert.checks_sound_everywhere` from it and `total_has_value`), resting on
# the lemmas below about what each connective means (`two_valued`,
# `and_meaning` and the rest); monotonicity (`monotone`), and `not fails`
# for partial models from it (`cert.not_refuted`). The `Invalid` theorem
# is still owed; for it, so far, a definite answer of unfolding is the
# answer at more fuel (`unfolding_more_fuel`).
#
# `before` is a strict total order on values (`before_irreflexive`,
# `before_transitive`, `before_total`). Every sort of a context without
# parameters has a value (`value_of_sort`): `value_of` gives one, from the
# kept witnesses, in every model whose arrays include the constant arrays
# its `konst` names. S6 also owes this, which this module is written to and
# states only in comments: two normal forms are equal exactly when they
# are the same function (so `normal_arrays` satisfies `arrays_ok`).
#
# **Every interpretation is a `Model`** (#85). `checks_sound` says "for
# every `Model` …"; that means "in every interpretation of the context"
# because each interpretation 𝔄 that satisfies the context, among the
# structures whose arrays include every `lambda`'s (above), gives a `Model`
# that satisfies the premises and evaluates the goal as 𝔄 does. 𝔄 is a
# mathematical object, not a Checkers value, so this is an argument, not a
# lemma; each step below is mathematics outside Checkers. What a `Model`
# holds, against SMT-LIB 2.6 (§5.3, Definitions 6 and 8, pp. 76–77):
#
# - `Bool`, `Int` and sequences are exact: `Truth`, `Integer` (any `Int`;
#   the theory `Ints` makes `Int` "the set of all integer numbers"),
#   `Sequence` (finite lists: SMT-LIB 2.6 has no sequences, and `ckc`
#   writes a Checkers array, finite, as one, SPEC §7.3).
# - A datatype's values are `Constructed` trees, finite, with fields of
#   their sorts (`of_sort`): the absolutely free algebra Definition 8 asks
#   for. A selector at another constructor's value is `wrong_sel`, of
#   which Definition 8 asks nothing but that it is of the field's sort
#   (Remark 11, p. 78).
# - An uninterpreted sort's elements are `Element 0 … Element n` (`UpTo n`)
#   or every `Element n` (`Countable`): any non-empty countable set, up to
#   numbering. An array sort's elements are the numbers `array_in` names:
#   any countable set.
# - A function, a definition and each unspecified result (`div_zero`,
#   `mod_zero`, `nth_out`, `wrong_sel`) is a function of exactly what SMT-LIB
#   or Z3 makes it a function of. A recursive definition is its declaration
#   and its equation (`definition_axiom`), as §4.2.3 (pp. 62–63) defines
#   `define-funs-rec`, so every solution is a `Model`'s.
#
# Toward the converse, a lemma: in a `Model` that answers every question
# (`gives`, `arrays_total_at`), every closed term of the context has a value
# of its sort (`total_has_value`). That alone doesn't make the model an
# interpretation: the array laws (`arrays_ok_at`) and the definitions'
# equations (`definition_axiom`) are premises of their own.
#
# **At the certificate's terms** (the first statement of `checks_sound`),
# that is all: restrict 𝔄 to the values of the finitely many terms the
# certificate uses, with the reads the premises ask there (`differ`'s
# index, `select` at it). That is finitely many elements, numbered
# `Element n` or `ArrayElem k`, and finitely many answers: a finite table,
# which is a `Model` value. It meets the premises there because 𝔄 meets
# them everywhere, and the goal, whose subterms are among those terms, has
# 𝔄's value because evaluation is compositional. Neither countability nor
# computability enters.
#
# **At all values** (the corollary), 𝔄 may be uncountable, and a `Model`'s
# domains are countable. Downward Löwenheim–Skolem gives a countable
# elementary substructure 𝔅 of 𝔄 for a countable signature
# (https://en.wikipedia.org/wiki/L%C3%B6wenheim%E2%80%93Skolem_theorem;
# many sorts reduce to one by relativization, Enderton, *A Mathematical
# Introduction to Logic*, §4.3). The signature is the context's symbols with
# a function symbol `F_t(ȳ)` for each `lambda` body `t` of the signature,
# whose `∀`-axiom is `select (F_t ȳ) i = t[i, ȳ]`: countably many. 𝔅 is still
# an SMT-LIB structure, by closure: `Int` holds every numeral and `-`, so it
# is ℤ; a sequence sort is closed under `seq.empty`, `seq.unit`, `seq.++`
# and `seq.nth`,
# so it is the finite sequences over 𝔅's element sort; a datatype sort is
# closed under constructors and selectors, so it is the free algebra over
# 𝔅's other sorts; the array laws are `∀` and `∀∃` sentences, which an
# elementary substructure keeps. Numbering 𝔅's elements makes it a `Model`.
# That `Model`'s functions need not be computable. A lemma proved "for every
# `m~Model`" covers it if a variable of function type ranges over every
# function, as §7.3's encoding into Z3's arrays reasons; SPEC does not say
# which reading it means: every function, or only those a program can
# write. #486 proposes every function.

module model

import std.list
import term (Name, Sort, Bool, Int, Seq, Arr, Data, Unin, Param, Ctor, FunDecl, Def, Axiom, Context, Sig)
import term (Witness, WTrue, WZero, WEmpty, WElement, WConst, WParam, WCon, WOf)
import term (Op, Not, And, Or, Implies, Ite, Eq, Add, Sub, Neg, Mul, Div, Mod, Lt, Le, Gt, Ge, Select, Store, MapAdd)
import term (SeqLen, SeqNth, SeqUnit, SeqConcat, SeqExtract)
import term (Head, Fun, Con, Is, Sel, Num, Boolean, Prim, ConstArr, EmptySeq, Term, Var, App, Let, Lam)
import term (Connective, Atom, ConstOf, NotOf, AndOf, OrOf, ImpliesOf, IteOf, IffOf)

# ── Values ───────────────────────────────────────────────────────────────────

# A value of some sort. A value doesn't record its sort: the term it is the
# value of has one, and `of_sort` says whether a value given by a model
# belongs to a sort.
#
# - `Truth b`, `Integer n`: a `Bool`, an `Int`.
# - `Sequence xs`: a `Seq`, its elements in order.
# - `Constructed k fields`: a datatype's value built by its `k`-th
#   constructor.
# - `Element n`: the `n`-th element of an uninterpreted sort (`declare-sort`).
#   Elements with different numbers are different.
# - `ArrayElem k`: the `k`-th element of an array sort, if the model names
#   it (`Model.array_in`). Elements with different numbers are different.
export enum Value
    Truth b              : b~Bool
    Integer n            : n~Int
    Sequence xs          : xs~List Value
    Constructed k fields : k~Nat, fields~List Value
    Element n            : n~Nat
    ArrayElem k          : k~Nat

# Why a term has no value here.
export enum Unknown
    # The model doesn't say: what `h` gives at these arguments (`Fun f` for
    # a function; `Prim Div` or `Prim Mod` for a division by zero; `Prim
    # SeqNth` for an index out of range; `Sel d k j` for a selector applied
    # to another constructor's value; `Prim Select`, `Prim Store`, `Prim
    # MapAdd` or `ConstArr s` for an array).
    NotGiven h : h~Head
    # The model doesn't say which array a `lambda` is.
    LambdaNotGiven
    # Evaluation needed more than `Model.fuel` levels (in `refutes` only).
    OutOfFuel
    # A call of a definition not marked terminating, in `refutes`.
    NotTerminating
    # The model gave a value that isn't of the sort needed.
    WrongSort
    # The term isn't a term of the context. Never for one that is.
    IllSorted

# The elements of an uninterpreted sort: `UpTo n` is `Element 0` to
# `Element n` (never empty, as SMT-LIB requires); `Countable` is every
# `Element n`; `Unsized` is a sort whose size the model doesn't say (Z3's
# `(get-value …)` values give elements but no universe): every `Element n`
# may be one, and whatever depends on how many there are isn't
# determined (no array over it is made by a store). Countable domains are
# all that is needed (Löwenheim–Skolem, see the module's comment).
export enum Domain
    UpTo n : n~Nat
    Countable
    Unsized

# An interpretation of a context's symbols, and of what SMT-LIB leaves
# unspecified. Each function may answer `None`: then the model doesn't say,
# and a term that needs it is `NotGiven`. A model that answers `Some`
# everywhere is complete.
#
# - `funs f vs`: the `f`-th function at arguments `vs`; a constant at `[]`.
# - `select s k i`: array `k` of sort `s` at index `i`.
# - `const s v`: the array of sort `s` that is `v` everywhere.
# - `store s k i v`: the array that is `k` with index `i` mapped to `v`.
# - `sum s k l`: the array that is `(_ map (+ (Int Int) Int))` of `k` and
#   `l`.
# - `lambda s env senv x body`: the array that is a `lambda` over a
#   variable of sort `x`, with the variables bound around it having the
#   values `env` (`Var 0` first) and the sorts `senv`.
# - `array_in s k`: whether `k` is an array of sort `s`.
# - `differ s k l`: an index where arrays `k` and `l` of `s` differ (for
#   extensionality: `ext_law`).
# - `div_zero n`, `mod_zero n`: `(div n 0)` and `(mod n 0)`. SMT-LIB leaves
#   them unspecified; each is a function of `n`, and the two are unrelated.
# - `nth_out e xs i`: `(seq.nth xs i)` for `i` outside `xs`, where the
#   elements are of sort `e`: a function of `xs` and `i`.
# - `wrong_sel d k j args v`: selector `j` of constructor `k` of datatype
#   `d` (at sort arguments `args`) applied to `v`, built by another
#   constructor: a function of `v`.
# - `domain u args`: the elements of `Unin u args`.
# - `fuel`: how many levels `refutes` may unfold definitions (see the
#   module's comment).
#
# What a model gives is checked against the sort needed (`of_sort`), so a
# model can't make a term take a value outside its sort.
export record Model
    funs~(Nat -> List Value -> Option Value)
    select~(Sort -> Nat -> Value -> Option Value)
    const~(Sort -> Value -> Option Nat)
    store~(Sort -> Nat -> Value -> Value -> Option Nat)
    sum~(Sort -> Nat -> Nat -> Option Nat)
    lambda~(Sort -> List Value -> List Sort -> Sort -> Term -> Option Nat)
    array_in~(Sort -> Nat -> Bool)
    differ~(Sort -> Nat -> Nat -> Value)
    div_zero~(Int -> Option Int)
    mod_zero~(Int -> Option Int)
    nth_out~(Sort -> List Value -> Int -> Option Value)
    wrong_sel~(Nat -> Nat -> Nat -> List Sort -> Value -> Option Value)
    domain~(Nat -> List Sort -> Domain)
    fuel~Nat

# A model whose functions and unspecified results are those given, and
# which has no arrays: every array question is `NotGiven`.
export fn without_arrays funs div_zero mod_zero nth_out wrong_sel domain fuel -> m : funs~(Nat -> List Value -> Option Value),
                                                                                     div_zero~(Int -> Option Int),
                                                                                     mod_zero~(Int -> Option Int),
                                                                                     nth_out~(Sort -> List Value -> Int -> Option Value),
                                                                                     wrong_sel~(Nat -> Nat -> Nat -> List Sort -> Value -> Option Value),
                                                                                     domain~(Nat -> List Sort -> Domain), fuel~Nat,
                                                                                     m~Model
    let select = \_ _ _ -> None
    let const = \_ _ -> None
    let store = \_ _ _ _ -> None
    let sum = \_ _ _ -> None
    let lambda = \_ _ _ _ _ -> None
    let array_in = \_ _ -> False
    let differ = \_ _ _ -> Truth False
    Model funs select const store sum lambda array_in differ div_zero mod_zero nth_out wrong_sel domain fuel

# ── Sorts of values ──────────────────────────────────────────────────────────

fn in_domain d n -> r : d~Domain, n~Nat, r~Bool
    match d
        UpTo last -> n <= last
        Countable -> True
        Unsized   -> True

# Whether `v`, given by the model, is a value of sort `s`. An array is one
# the model names as an element of its sort.
export fn of_sort c m s v -> r : c~Context, m~Model, s~Sort, v~Value, r~Bool
    match (s, v)
        (Bool, Truth _)                 -> True
        (Int, Integer _)                -> True
        (Seq e, Sequence xs)            -> all_of_sort c m e xs
        (Arr _ _, ArrayElem k)          -> m.array_in s k
        (Data d args, Constructed k fs) ->
            match term.ctor (term.signature c) d k
                Some k_ctor -> fields_of_sort c m (list.map (term.instantiate args) (term.field_sorts k_ctor.fields)) fs
                None        -> False
        (Unin u args, Element n)        -> in_domain (m.domain u args) n
        _                               -> False

fn all_of_sort c m s vs -> r : c~Context, m~Model, s~Sort, vs~List Value, r~Bool
    match vs
        []        -> True
        v :: rest -> of_sort c m s v and all_of_sort c m s rest

fn fields_of_sort c m ss vs -> r : c~Context, m~Model, ss~List Sort, vs~List Value, r~Bool
    match (ss, vs)
        ([], [])           -> True
        (s :: sr, v :: vr) -> of_sort c m s v and fields_of_sort c m sr vr
        _                  -> False

# What the model said, `got`, for a term of sort `s` that needs `h`.
fn given c m s h got -> r : c~Context, m~Model, s~Sort, h~Head, got~Option Value, r~Result Value Unknown
    match got
        None   -> Err (NotGiven h)
        Some v -> if of_sort c m s v then Ok v else Err WrongSort

# The array of sort `s` the model named, `got`; `missing` if none.
fn given_array c m s missing got -> r : c~Context, m~Model, s~Sort, missing~Unknown, got~Option Nat,
                                        r~Result Value Unknown
    match got
        None   -> Err missing
        Some k -> if m.array_in s k then Ok (ArrayElem k) else Err WrongSort

# ── A value of every sort ────────────────────────────────────────────────────
# Every sort of a context has a value: that is what accepting a datatype
# rests on (`term.fits`). `value_of` writes one: for a datatype, its kept
# witness (`Sig.values`) at values of its arguments; for an uninterpreted
# sort, `Element 0`, which every domain has; for an array sort, the
# constant array `konst` names for a value of its element sort.

# A value of sort `s` (with no `Param` in it), if `sig` has one.
export fn value_of sig konst s -> r : sig~Sig, konst~(Sort -> Value -> Option Nat), s~Sort, r~Option Value
    match s
        Bool        -> Some (Truth True)
        Int         -> Some (Integer 0)
        Seq _       -> Some (Sequence [])
        Unin _ _    -> Some (Element 0)
        Arr _ w     ->
            match value_of sig konst w
                Some v ->
                    match konst s v
                        Some k -> Some (ArrayElem k)
                        None   -> None
                None   -> None
        Data d args ->
            match values_of sig konst args
                Some vs -> kept_at sig konst d args vs
                None    -> None
        Param _     -> None

fn values_of sig konst ss -> r : sig~Sig, konst~(Sort -> Value -> Option Nat), ss~List Sort, r~Option (List Value)
    match ss
        []        -> Some []
        s :: rest ->
            match (value_of sig konst s, values_of sig konst rest)
                (Some v, Some vs) -> Some (v :: vs)
                _                 -> None

# Witness `w` of a value of template sort `t` (whose `Param k` is `args`'
# `k`-th sort), where `WParam k` is `vs`' `k`-th value; it is part of
# datatype `d`'s kept witness, so a `WOf e` in it has `e < d`.
fn witness_value sig konst d args vs w t -> r : sig~Sig, konst~(Sort -> Value -> Option Nat), d~Nat, args~List Sort,
                                                vs~List Value, w~Witness, t~Sort, r~Option Value
    decreasing (d, witness_size w)
    match (w, t)
        (WTrue, Bool)             -> Some (Truth True)
        (WZero, Int)              -> Some (Integer 0)
        (WEmpty, Seq _)           -> Some (Sequence [])
        (WElement, Unin _ _)      -> Some (Element 0)
        (WConst v, Arr _ e)       ->
            match witness_value sig konst d args vs v e
                Some x ->
                    match konst (term.instantiate args t) x
                        Some k -> Some (ArrayElem k)
                        None   -> None
                None   -> None
        (WParam k, Param _)       -> list.head (list.drop k vs)
        (WCon k fs, Data e targs) ->
            match term.ctor sig e k
                Some c ->
                    match witness_values sig konst d args vs fs (list.map (term.instantiate targs) (term.field_sorts c.fields))
                        Some xs -> Some (Constructed k xs)
                        None    -> None
                None   -> None
        (WOf e ws, Data _ targs)  ->
            if e < d
                match witness_values sig konst d args vs ws targs
                    Some xs -> kept_at sig konst e (list.map (term.instantiate args) targs) xs
                    None    -> None
            else
                None
        _                         -> None

fn witness_values sig konst d args vs ws ts -> r : sig~Sig, konst~(Sort -> Value -> Option Nat), d~Nat, args~List Sort,
                                                   vs~List Value, ws~List Witness, ts~List Sort, r~Option (List Value)
    decreasing (d, witnesses_size ws)
    match (ws, ts)
        ([], [])           -> Some []
        (w :: wr, t :: tr) ->
            match (witness_value sig konst d args vs w t, witness_values sig konst d args vs wr tr)
                (Some x, Some xs) -> Some (x :: xs)
                _                 -> None
        _                  -> None

# Datatype `e`'s kept witness at arguments `args`, whose values are `vs`
# (from inside a witness, `e` is before the datatype the witness belongs
# to).
fn kept_at sig konst e args vs -> r : sig~Sig, konst~(Sort -> Value -> Option Nat), e~Nat, args~List Sort, vs~List Value,
                                      r~Option Value
    decreasing (e, witness_size (if e < len sig.values then sig.values[e] else WTrue) + 1)
    if e < len sig.values and e < len sig.datatypes
        witness_value sig konst e args vs sig.values[e] (Data e (term.params_of (list.length sig.datatypes[e].params) 0))
    else
        None

fn witness_size w -> n : w~Witness, n~Nat
    match w
        WConst v  -> 1 + witness_size v
        WCon _ fs -> 1 + witnesses_size fs
        WOf _ ws  -> 1 + witnesses_size ws
        _         -> 1

fn witnesses_size ws -> n : ws~List Witness, n~Nat
    match ws
        []        -> 1
        w :: rest -> 1 + witness_size w + witnesses_size rest

# What `value_of` gave for sort `s` is a value of it in `m`.
export fn sort_value c m s r -> b : c~Context, m~Model, s~Sort, r~Option Value, b~Bool
    match r
        Some v -> of_sort c m s v
        None   -> False

# What `konst` gave for the array sort `s` is an array of it in `m`.
export fn konst_in m s r -> b : m~Model, s~Sort, r~Option Nat, b~Bool
    match r
        Some k -> m.array_in s k
        None   -> False

# What `sort_value` and `konst_in` are, for other modules (their bodies are
# sealed there): to give `value_of_sort` its premise and use its
# conclusion.
export lemma sort_value_def c m s r : c~Context, m~Model, s~Sort, r~Option Value
    ensures sort_value c m s r
        == match r
            Some v -> of_sort c m s v
            None   -> False

export lemma konst_in_def m s r : m~Model, s~Sort, r~Option Nat
    ensures konst_in m s r
        == match r
            Some k -> m.array_in s k
            None   -> False

# Every sort of a context with no parameter free in it has a value:
# `value_of` gives one, in every model whose arrays include the constant
# arrays `konst` names at the context's array sorts. It rests on `term.datatypes_hold`: each datatype's kept witness
# fits its sort, with the datatypes before it accepted.
export lemma value_of_sort c m konst s : c~Context, m~Model, konst~(Sort -> Value -> Option Nat), s~Sort,
                                         closed: term.sort_ok (term.signature c) 0 s,
                                         constants: forall i w v : i~Sort, w~Sort, v~Value,
                                         term.sort_ok (term.signature c) 0 (Arr i w) and of_sort c m w v implies konst_in m (Arr i w) (konst (Arr i w) v)
    ensures sort_value c m s (value_of (term.signature c) konst s)
    proof
        let sig = term.signature c
        match s
            Arr i w     ->
                have value_of_sort c m konst w
                match value_of sig konst w
                    Some v -> have constants i w v
                    None   -> auto
            Data d args ->
                have values_sort c m konst args
                match values_of sig konst args
                    Some vs -> have kept_sort c m konst d args vs
            Unin u args -> have zero_in m.domain u args
            _           -> auto

# The values `values_of` gives for sorts with no parameter free are of
# those sorts.
lemma values_sort c m konst ss : c~Context, m~Model, konst~(Sort -> Value -> Option Nat), ss~List Sort,
                                 closed: term.sorts_ok (term.signature c) 0 ss,
                                 constants: forall i w v : i~Sort, w~Sort, v~Value,
                                 term.sort_ok (term.signature c) 0 (Arr i w) and of_sort c m w v implies konst_in m (Arr i w) (konst (Arr i w) v)
    ensures match values_of (term.signature c) konst ss
        Some vs -> fields_of_sort c m ss vs
        None    -> False
    proof
        match ss
            []        -> auto
            s :: rest ->
                have value_of_sort c m konst s
                have values_sort c m konst rest

# Datatype `e`'s kept witness, at arguments `args` whose values are `vs`,
# is a value of `(e args)`.
lemma kept_sort c m konst e args vs : c~Context, m~Model, konst~(Sort -> Value -> Option Nat), e~Nat, args~List Sort,
                                      vs~List Value, e < len (term.signature c).datatypes,
                                      list.length args == list.length (term.signature c).datatypes[e].params,
                                      closed: term.sorts_ok (term.signature c) 0 args, fields_of_sort c m args vs,
                                      constants: forall i w v : i~Sort, w~Sort, v~Value,
                                      term.sort_ok (term.signature c) 0 (Arr i w) and of_sort c m w v implies konst_in m (Arr i w) (konst (Arr i w) v)
    ensures sort_value c m (Data e args) (kept_at (term.signature c) konst e args vs)
    proof
        decreasing (e, witness_size (if e < len (term.signature c).values then (term.signature c).values[e] else WTrue) + 2)
        let sig = term.signature c
        let n = list.length sig.datatypes[e].params
        have term.datatypes_hold c e
        have term.datatype_ok_def sig e
        have term.instantiate_params args n 0
        have term.instantiate_def args (Data e (term.params_of n 0))
        have witness_sort c m konst e args vs sig.values[e] (Data e (term.params_of n 0))

# Witness `w`, part of datatype `d`'s kept witness and fitting template
# sort `t` (whose parameters are `args`, with values `vs`), gives a value
# of `t` at `args`.
lemma witness_sort c m konst d args vs w t : c~Context, m~Model, konst~(Sort -> Value -> Option Nat), d~Nat,
                                             args~List Sort, vs~List Value, w~Witness, t~Sort,
                                             term.fits (term.signature c) d (list.length args) w t,
                                             closed: term.sort_ok (term.signature c) 0 (term.instantiate args t),
                                             fields_of_sort c m args vs,
                                             constants: forall i w2 v : i~Sort, w2~Sort, v~Value,
                                             term.sort_ok (term.signature c) 0 (Arr i w2) and of_sort c m w2 v implies konst_in m (Arr i w2) (konst (Arr i w2) v)
    ensures sort_value c m (term.instantiate args t) (witness_value (term.signature c) konst d args vs w t)
    proof
        decreasing (d, witness_size w + 1)
        let sig = term.signature c
        have term.fits_def sig d (list.length args) w t
        have term.instantiate_def args t
        match (w, t)
            (WConst v, Arr i e)       ->
                have witness_sort c m konst d args vs v e
                match witness_value sig konst d args vs v e
                    Some x ->
                        let a = Arr (term.instantiate args i) (term.instantiate args e)
                        have constants (term.instantiate args i) (term.instantiate args e) x
                        match konst a x
                            Some k -> have of_sort c m a (ArrayElem k) == m.array_in a k
                    None   -> auto
            (WParam k, Param _)       -> have field_at c m args vs k
            (WCon k fs, Data e targs) ->
                match term.ctor sig e k
                    Some k_ctor ->
                        let fields = term.field_sorts k_ctor.fields
                        have term.datatypes_hold c e
                        have term.datatype_ok_def sig e
                        have term.ctor_fields_ok sig (list.length targs) sig.datatypes[e].ctors k k_ctor
                        have term.instantiate_twice_all sig targs args fields
                        have term.instantiates_ok sig (list.length targs) (list.map (term.instantiate args) targs) fields
                        have witness_sorts c m konst d args vs fs (list.map (term.instantiate targs) fields)
                        match witness_values sig konst d args vs fs (list.map (term.instantiate targs) fields)
                            Some xs ->
                                have of_sort c m (Data e (list.map (term.instantiate args) targs)) (Constructed k xs)
                                    == fields_of_sort c m (list.map (term.instantiate (list.map (term.instantiate args) targs)) fields) xs
            (WOf e ws, Data _ targs)  ->
                have list.length_map (term.instantiate args) targs
                have witness_sorts c m konst d args vs ws targs
                match witness_values sig konst d args vs ws targs
                    Some xs -> have kept_sort c m konst e (list.map (term.instantiate args) targs) xs
            (WElement, Unin u targs)  ->
                have zero_in m.domain u (list.map (term.instantiate args) targs)
            _                         -> auto

lemma witness_sorts c m konst d args vs ws ts : c~Context, m~Model, konst~(Sort -> Value -> Option Nat), d~Nat,
                                                args~List Sort, vs~List Value, ws~List Witness, ts~List Sort,
                                                term.fits_all (term.signature c) d (list.length args) ws ts,
                                                closed: term.sorts_ok (term.signature c) 0 (list.map (term.instantiate args) ts),
                                                fields_of_sort c m args vs,
                                                constants: forall i w2 v : i~Sort, w2~Sort, v~Value,
                                                term.sort_ok (term.signature c) 0 (Arr i w2) and of_sort c m w2 v implies konst_in m (Arr i w2) (konst (Arr i w2) v)
    ensures match witness_values (term.signature c) konst d args vs ws ts
        Some xs -> fields_of_sort c m (list.map (term.instantiate args) ts) xs
        None    -> False
    proof
        decreasing (d, witnesses_size ws + 1)
        have term.fits_all_def (term.signature c) d (list.length args) ws ts
        match (ws, ts)
            ([], [])           -> auto
            (w :: wr, t :: tr) ->
                have witness_sort c m konst d args vs w t
                have witness_sorts c m konst d args vs wr tr

# Every domain has `Element 0`.
lemma zero_in dom u args : dom~(Nat -> List Sort -> Domain), u~Nat, args~List Sort
    ensures in_domain (dom u args) 0
    proof
        match dom u args
            UpTo _    -> auto
            Countable -> auto
            Unsized   -> auto

# The `k`-th of values of sorts `ss` is of the `k`-th sort.
lemma field_at c m ss vs k : c~Context, m~Model, ss~List Sort, vs~List Value, k~Nat, fields_of_sort c m ss vs,
                             k < list.length ss
    ensures match (list.head (list.drop k ss), list.head (list.drop k vs))
        (Some s, Some v) -> of_sort c m s v
        _                -> False
    proof
        match (ss, vs)
            (_ :: sr, _ :: vr) -> if k == 0 then auto else have field_at c m sr vr (k - 1)
            _                  -> auto

# ── Numbering normal forms ───────────────────────────────────────────────────
# The model `refutes` builds names each array by a number: its normal form
# (`Form`) written as bytes (`form_bytes`) and read as a base-256 number
# after a leading 1, so that the number's size grows with the form's.
# `decode` reads it back. An array inside a form is written as its number,
# which is smaller than the number of the form holding it.

# A normal form: `base` everywhere except at the indices of `stores`.
export record Form
    base~Value
    stores~List (Value, Value)

export fn code f -> n : f~Form, n~Nat
    number_of (1 :: form_bytes f) 0

fn number_of ds acc -> n : ds~List Nat, acc~Nat, n~Nat
    match ds
        []        -> acc
        d :: rest -> number_of rest (acc * 256 + d)

fn form_bytes f -> bs : f~Form, bs~List Nat
    value_bytes f.base ++ nat_bytes (list.length f.stores) ++ stores_bytes f.stores

fn stores_bytes st -> bs : st~List (Value, Value), bs~List Nat
    match st
        []             -> []
        (j, x) :: rest -> value_bytes j ++ value_bytes x ++ stores_bytes rest

fn value_bytes v -> bs : v~Value, bs~List Nat
    match v
        Truth b          -> [0, if b then 1 else 0]
        Integer n        -> if n >= 0 then 1 :: 0 :: nat_bytes n else 1 :: 1 :: nat_bytes (0 - n)
        Sequence xs      -> 2 :: nat_bytes (list.length xs) ++ values_bytes xs
        Constructed k fs -> 3 :: nat_bytes k ++ nat_bytes (list.length fs) ++ values_bytes fs
        Element n        -> 4 :: nat_bytes n
        ArrayElem k      -> 5 :: nat_bytes k

fn values_bytes vs -> bs : vs~List Value, bs~List Nat
    match vs
        []        -> []
        v :: rest -> value_bytes v ++ values_bytes rest

# `n` in seven-bit groups, lowest first, each but the last with 128 added.
fn nat_bytes n -> bs : n~Nat, bs~List Nat
    decreasing n
    if n < 128 then [n] else (128 + n % 128) :: nat_bytes (n / 128)

# The form numbered `n`, if `n` numbers one.
export fn decode n -> r : n~Nat, r~Option Form
    match digits_of n []
        1 :: bs ->
            match read_form bs
                Some (f, []) -> Some f
                _            -> None
        _       -> None

fn digits_of n acc -> ds : n~Nat, acc~List Nat, ds~List Nat
    decreasing n
    if n == 0 then acc else digits_of (n / 256) (n % 256 :: acc)

# Whether reading left `rest` shorter than `bs`.
fn shorter r bs -> b : r~Option (a, List Nat), bs~List Nat, b~Bool
    match r
        Some (_, rest) -> list.length rest < list.length bs
        None           -> True

fn read_form bs -> r : bs~List Nat, r~Option (Form, List Nat)
    match read_value bs
        Some (base, rest) ->
            match read_nat rest
                Some (n, more) ->
                    match read_stores n more
                        Some (st, left) -> Some (Form base st, left)
                        None            -> None
                None           -> None
        None              -> None

fn read_nat bs -> r : bs~List Nat, r~Option (Nat, List Nat), shorter r bs
    match bs
        []        -> None
        d :: rest ->
            if d < 128
                Some (d, rest)
            else if d < 256
                match read_nat rest
                    Some (n, more) -> Some (d - 128 + 128 * n, more)
                    None           -> None
            else
                None

fn read_value bs -> r : bs~List Nat, r~Option (Value, List Nat), shorter r bs
    decreasing (list.length bs, 1)
    match bs
        0 :: b :: rest -> if b == 0 then Some (Truth False, rest) else if b == 1 then Some (Truth True, rest) else None
        1 :: s :: rest ->
            match read_nat rest
                Some (n, more) -> if s == 0 then Some (Integer n, more) else if s == 1 then Some (Integer (0 - n), more) else None
                None           -> None
        2 :: rest      ->
            match read_nat rest
                Some (n, more) ->
                    match read_values n more
                        Some (xs, left) -> Some (Sequence xs, left)
                        None            -> None
                None           -> None
        3 :: rest      ->
            match read_nat rest
                Some (k, more) ->
                    match read_nat more
                        Some (n, after) ->
                            match read_values n after
                                Some (fs, left) -> Some (Constructed k fs, left)
                                None            -> None
                        None            -> None
                None           -> None
        4 :: rest      ->
            match read_nat rest
                Some (n, more) -> Some (Element n, more)
                None           -> None
        5 :: rest      ->
            match read_nat rest
                Some (k, more) -> Some (ArrayElem k, more)
                None           -> None
        _              -> None

fn read_values n bs -> r : n~Nat, bs~List Nat, r~Option (List Value, List Nat), shorter r bs or n == 0
    decreasing (list.length bs, 2)
    if n == 0
        Some ([], bs)
    else
        match read_value bs
            Some (v, rest) ->
                match read_values (n - 1) rest
                    Some (vs, left) -> Some (v :: vs, left)
                    None            -> None
            None           -> None

fn read_stores n bs -> r : n~Nat, bs~List Nat, r~Option (List (Value, Value), List Nat)
    decreasing list.length bs
    if n == 0
        Some ([], bs)
    else
        match read_value bs
            Some (j, rest) ->
                match read_value rest
                    Some (x, more) ->
                        match read_stores (n - 1) more
                            Some (st, left) -> Some ((j, x) :: st, left)
                            None            -> None
                    None           -> None
            None           -> None

# ── Normal forms ─────────────────────────────────────────────────────────────
# An array is named by one normal form: its constant `base` and the stores
# that differ from it, each index once, in order (`before`). How depends on
# the index sort (`index_kind`), given the model's domains:
#
# - `Listed es`, a finite sort whose elements are `es` (`Bool`, an
#   uninterpreted sort with `UpTo n`): the base is the value at the first of
#   `es`, and stores are at the others;
# - `Unbounded`, a sort this module can write a value of outside any finite
#   set (`fresh`): `Int`, `(Seq e)` for any `e` with a value (`value_of`),
#   an uninterpreted sort with `Countable` elements, `(Array i w)` with `w`
#   unbounded; stores anywhere;
# - `Opaque`, a datatype or any other sort: only constant arrays are named.
#
# Two normal forms are meant to be equal exactly when the arrays are the
# same function (not proved here; S6 owes it): if their bases differ, they differ at the first listed element, at an
# index stored in neither (`fresh`), or, for constant arrays, anywhere (no
# sort is empty); if their bases agree, at a stored index.
#
# "No sort is empty" and "`(Seq e)` is unbounded" rest on every sort of a
# context having a value: `value_of_sort` proves that `value_of` gives one,
# in a model whose arrays include the constant arrays `konst` names. That
# the normal forms' `konst` (below) names arrays of `normal_arrays` is part
# of what S6 owes about normal forms. `fresh` and `normal_differ` find their
# index by computing it, and a sort `value_of` gave none for would make
# them answer `Truth False`.

# How normal forms are made at an index sort.
enum Kind
    Listed es : es~List Value
    Unbounded
    Opaque

# A listed domain is enumerated; one with more than `LISTED` elements is
# treated as `Opaque` (only constant arrays named), so that a model with a
# huge domain makes `refutes` slower to say less, not hang.
let LISTED = 1024

fn index_kind sig dom i -> k : sig~Sig, dom~(Nat -> List Sort -> Domain), i~Sort, k~Kind
    match i
        Bool        -> Listed [Truth False, Truth True]
        Unin u args ->
            match dom u args
                UpTo n    -> if n < LISTED then Listed (elements_upto n) else Opaque
                Countable -> Unbounded
                Unsized   -> Opaque
        _           -> if unbounded sig dom i then Unbounded else Opaque

# `Element 0`, …, `Element n`.
fn elements_upto n -> es : n~Nat, es~List Value
    elements_from 0 (n + 1)

fn elements_from k count -> es : k~Nat, count~Nat, es~List Value
    if count == 0 then [] else Element k :: elements_from (k + 1) (count - 1)

# The number of the constant array of `v`, at any array sort: its normal
# form has no stores, whatever the index sort, so `s` isn't needed (it is
# there to fit `value_of`'s `konst`).
fn constant_number s v -> r : s~Sort, v~Value, r~Option Nat
    Some (code (Form v []))

# Whether this module can write a value of `s` outside any finite set.
fn unbounded sig dom s -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, r~Bool
    match s
        Int         -> True
        Seq e       -> value_of sig constant_number e != None
        Unin u args -> dom u args == Countable
        Arr _ w     -> unbounded sig dom w
        _           -> False

# A strict total order on values (by constructor, then by contents):
# `before_irreflexive`, `before_transitive`, `before_total` below.
fn before a b -> r : a~Value, b~Value, r~Bool
    match (a, b)
        (Truth x, Truth y)                   -> not x and y
        (Integer x, Integer y)               -> x < y
        (Sequence xs, Sequence ys)           -> all_before xs ys
        (Constructed k xs, Constructed l ys) -> k < l or (k == l and all_before xs ys)
        (Element x, Element y)               -> x < y
        (ArrayElem k, ArrayElem l)           -> k < l
        _                                    -> rank a < rank b

fn rank v -> r : v~Value, r~Nat
    match v
        Truth _         -> 0
        Integer _       -> 1
        Sequence _      -> 2
        Constructed _ _ -> 3
        Element _       -> 4
        ArrayElem _     -> 5

# Lists compared element by element, a shorter one first when it is a
# prefix of the other.
fn all_before xs ys -> r : xs~List Value, ys~List Value, r~Bool
    match (xs, ys)
        ([], [])           -> False
        ([], _)            -> True
        (_, [])            -> False
        (x :: xr, y :: yr) -> before x y or (x == y and all_before xr yr)

# A value of unbounded sort `s` that isn't one of `used`: an integer or an
# element above them all, a sequence longer than them all, a constant
# array whose constant is none of theirs.
fn fresh sig s used -> r : sig~Sig, s~Sort, used~List Value, r~Option Value
    match s
        Int      -> Some (Integer (1 + max_int used))
        Unin _ _ -> Some (Element (1 + max_element used))
        Seq e    ->
            match value_of sig constant_number e
                Some d -> Some (Sequence (repeat (1 + max_length used) d))
                None   -> None
        Arr _ w  ->
            match fresh sig w (bases used)
                Some b -> Some (ArrayElem (code (Form b [])))
                None   -> None
        _        -> None

fn max_element vs -> r : vs~List Value, r~Nat
    match vs
        []                -> 0
        Element n :: rest -> if n > max_element rest then n else max_element rest
        _ :: rest         -> max_element rest

fn max_int vs -> r : vs~List Value, r~Int
    match vs
        []                -> 0
        Integer n :: rest -> if n > max_int rest then n else max_int rest
        _ :: rest         -> max_int rest

fn max_length vs -> r : vs~List Value, r~Nat
    match vs
        []                  -> 0
        Sequence xs :: rest -> if list.length xs > max_length rest then list.length xs else max_length rest
        _ :: rest           -> max_length rest

fn repeat n x -> r : n~Nat, x~Value, r~List Value
    if n == 0 then [] else x :: repeat (n - 1) x

# The constants of the arrays numbered by `vs`.
fn bases vs -> r : vs~List Value, r~List Value
    match vs
        []                  -> []
        ArrayElem k :: rest ->
            match decode k
                Some f -> f.base :: bases rest
                None   -> bases rest
        _ :: rest           -> bases rest

# Whether `base` and `stores` are a normal form at index sort `i`.
fn canonical sig dom i base stores -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), i~Sort, base~Value,
                                          stores~List (Value, Value), r~Bool
    if stores == []
        True
    else
        match index_kind sig dom i
            Listed es -> sorted_stores stores and no_store_of base stores and all_listed (list.drop 1 es) stores
            Unbounded -> sorted_stores stores and no_store_of base stores
            Opaque    -> False

fn all_listed es st -> r : es~List Value, st~List (Value, Value), r~Bool
    match st
        []             -> True
        (j, _) :: rest -> list.contains es j and all_listed es rest

fn sorted_stores st -> r : st~List (Value, Value), r~Bool
    match st
        []                       -> True
        [_]                      -> True
        (j, _) :: (k, x) :: rest -> before j k and sorted_stores ((k, x) :: rest)

fn no_store_of base st -> r : base~Value, st~List (Value, Value), r~Bool
    match st
        []             -> True
        (_, x) :: rest -> x != base and no_store_of base rest

# What `stores` hold at `i`, the first store at `i` hiding later ones, or
# `base`.
fn read_stores_at stores base i -> r : stores~List (Value, Value), base~Value, i~Value, r~Value
    match stores
        []             -> base
        (j, x) :: rest -> if j == i then x else read_stores_at rest base i

# `(j, x)` put in `st`, which is sorted, in its place, replacing a store at
# `j`.
fn insert_store j x st -> r : j~Value, x~Value, st~List (Value, Value), r~List (Value, Value)
    match st
        []             -> [(j, x)]
        (k, y) :: rest ->
            if j == k then (j, x) :: rest else if before j k then (j, x) :: st else (k, y) :: insert_store j x rest

fn drop_base base st -> r : base~Value, st~List (Value, Value), r~List (Value, Value)
    match st
        []             -> []
        (j, x) :: rest -> if x == base then drop_base base rest else (j, x) :: drop_base base rest

# `stores` sorted by index, the first store at an index hiding later ones.
fn sort_stores stores -> r : stores~List (Value, Value), r~List (Value, Value)
    match stores
        []             -> []
        (j, x) :: rest -> insert_store j x (sort_stores rest)

# The normal form of `base` with `stores` (the first store at an index
# hiding later ones), for index sort `i`.
fn normalize sig dom i base stores -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), i~Sort, base~Value,
                                          stores~List (Value, Value), r~Option Form
    match index_kind sig dom i
        Listed es ->
            match es
                first :: others ->
                    let at_first = read_stores_at stores base first
                    Some (Form at_first (listed_stores others stores base at_first))
                []              -> None
        Unbounded -> Some (Form base (drop_base base (sort_stores stores)))
        Opaque    -> if stores == [] then Some (Form base []) else None

# The stores at `es` (in order) of `stores` over `base`, but those equal to
# `at_first`.
fn listed_stores es stores base at_first -> r : es~List Value, stores~List (Value, Value), base~Value, at_first~Value,
                                                r~List (Value, Value)
    match es
        []        -> []
        e :: rest ->
            let x = read_stores_at stores base e
            if x == at_first then listed_stores rest stores base at_first else (e, x) :: listed_stores rest stores base at_first

# The index sort of array sort `s`.
fn index_of s -> r : s~Sort, r~Option Sort
    match s
        Arr i _ -> Some i
        _       -> None

fn numbered r -> n : r~Option Form, n~Option Nat
    match r
        Some f -> Some (code f)
        None   -> None

fn normal_const sig dom s v -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, v~Value, r~Option Nat
    match index_of s
        Some i -> numbered (normalize sig dom i v [])
        None   -> None

fn normal_store sig dom s k j x -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, k~Nat, j~Value, x~Value,
                                       r~Option Nat
    match (index_of s, decode k)
        (Some i, Some f) -> numbered (normalize sig dom i f.base ((j, x) :: f.stores))
        _                -> None

fn normal_select k i -> r : k~Nat, i~Value, r~Option Value
    match decode k
        Some f -> Some (read_stores_at f.stores f.base i)
        None   -> None

# `a` plus `b` at every index, for arrays of `Int`s.
fn normal_sum sig dom s a b -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, a~Nat, b~Nat, r~Option Nat
    match (index_of s, decode a, decode b)
        (Some i, Some f, Some g) ->
            match (f.base, g.base)
                (Integer x, Integer y) ->
                    match sums_at f.stores g.stores f.base g.base (list.keys f.stores ++ list.keys g.stores)
                        Some st -> numbered (normalize sig dom i (Integer (x + y)) st)
                        None    -> None
                _                      -> None
        _                        -> None

fn sums_at sa sb ba bb is -> r : sa~List (Value, Value), sb~List (Value, Value), ba~Value, bb~Value, is~List Value,
                                 r~Option (List (Value, Value))
    match is
        []        -> Some []
        j :: rest ->
            match (read_stores_at sa ba j, read_stores_at sb bb j, sums_at sa sb ba bb rest)
                (Integer p, Integer q, Some st) -> Some ((j, Integer (p + q)) :: st)
                _                               -> None

# An index where the arrays numbered `a` and `b` of array sort `s` differ,
# if they are different normal forms: where their bases differ, the first
# listed element, an index stored in neither, or any index; else the first
# stored index where they differ.
fn normal_differ sig dom s a b -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, a~Nat, b~Nat, r~Value
    match (index_of s, decode a, decode b)
        (Some i, Some f, Some g) ->
            if f.base != g.base
                match index_kind sig dom i
                    Listed (e :: _) -> e
                    Unbounded       -> or_any (fresh sig i (list.keys f.stores ++ list.keys g.stores))
                    _               -> or_any (value_of sig constant_number i)
            else
                first_difference f.stores g.stores f.base (list.keys f.stores ++ list.keys g.stores)
        _                        -> Truth False

fn or_any r -> v : r~Option Value, v~Value
    match r
        Some x -> x
        None   -> Truth False

fn first_difference sa sb base is -> r : sa~List (Value, Value), sb~List (Value, Value), base~Value, is~List Value,
                                         r~Value
    match is
        []        -> Truth False
        j :: rest ->
            if read_stores_at sa base j != read_stores_at sb base j then j else first_difference sa sb base rest

# Whether `k` is the number of a normal form of array sort `s`: `code` of
# what it decodes to (one number per form: bytes that read back the same,
# such as a padded group or "-0", aren't its number), canonical, with a base
# and stores of the sorts `s` needs. An array inside it has a smaller
# number (it is written inside `k`'s bytes), which is what ends the check.
export fn normal_in sig dom s k -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, k~Nat, r~Bool
    decreasing (k + 1, 0)
    match (s, decode k)
        (Arr i w, Some f) ->
            code f == k and canonical sig dom i f.base f.stores and normal_value sig dom w f.base k
                and normal_stores sig dom i w f.stores k
        _                 -> False

# One number per array: two arrays of the normal forms' model that decode
# to the same normal form are the same number (each is `code` of it).
export lemma one_number sig dom s k l : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, k~Nat, l~Nat,
                                        normal_in sig dom s k, normal_in sig dom s l, decode k == decode l
    ensures k == l

# Whether `v` is a value of sort `s` in the built model, where the arrays
# in it number less than `bound`.
fn normal_value sig dom s v bound -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, v~Value, bound~Nat, r~Bool
    decreasing (bound, value_size v)
    match (s, v)
        (Bool, Truth _)                 -> True
        (Int, Integer _)                -> True
        (Seq e, Sequence xs)            -> normal_values sig dom e xs bound
        (Arr _ _, ArrayElem k)          -> k < bound and normal_in sig dom s k
        (Data d args, Constructed k fs) ->
            match term.ctor sig d k
                Some c -> normal_fields sig dom (list.map (term.instantiate args) (term.field_sorts c.fields)) fs bound
                None   -> False
        (Unin u args, Element n)        -> in_domain (dom u args) n
        _                               -> False

fn normal_values sig dom s vs bound -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, vs~List Value, bound~Nat,
                                           r~Bool
    decreasing (bound, values_size vs)
    match vs
        []        -> True
        v :: rest -> normal_value sig dom s v bound and normal_values sig dom s rest bound

fn normal_fields sig dom ss vs bound -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), ss~List Sort, vs~List Value,
                                            bound~Nat, r~Bool
    decreasing (bound, values_size vs)
    match (ss, vs)
        ([], [])           -> True
        (s :: sr, v :: vr) -> normal_value sig dom s v bound and normal_fields sig dom sr vr bound
        _                  -> False

fn normal_stores sig dom i w st bound -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), i~Sort, w~Sort,
                                             st~List (Value, Value), bound~Nat, r~Bool
    decreasing (bound, stores_size st)
    match st
        []             -> True
        (j, x) :: rest ->
            normal_value sig dom i j bound and normal_value sig dom w x bound and normal_stores sig dom i w rest bound

fn value_size v -> n : v~Value, n~Nat
    match v
        Sequence xs      -> 1 + values_size xs
        Constructed _ fs -> 1 + values_size fs
        _                -> 1

fn values_size vs -> n : vs~List Value, n~Nat
    match vs
        []        -> 1
        v :: rest -> 1 + value_size v + values_size rest

fn stores_size st -> n : st~List (Value, Value), n~Nat
    match st
        []             -> 1
        (j, x) :: rest -> 1 + value_size j + value_size x + stores_size rest

# `m` with its arrays replaced by the normal forms' model: an array is the
# number of a normal form of its sort (`normal_in`); constant arrays,
# stores and `map +` make normal forms; a normal form is read by its
# stores; a `lambda` is not given. This is the model `refutes` evaluates
# in; `m`'s own arrays are not used.
export fn normal_arrays sig m -> r : sig~Sig, m~Model, r~Model
    let dom = m.domain
    let select = \_ k i -> normal_select k i
    let const = \s v -> normal_const sig dom s v
    let store = \s k j x -> normal_store sig dom s k j x
    let sum = \s a b -> normal_sum sig dom s a b
    let lambda = \_ _ _ _ _ -> None
    let array_in = \s k -> normal_in sig dom s k
    let differ = \s a b -> normal_differ sig dom s a b
    Model m.funs select const store sum lambda array_in differ m.div_zero m.mod_zero m.nth_out m.wrong_sel dom m.fuel

# The array Z3's `((as const s) v)` is in the normal forms' model, with
# the domains `dom`: for the readers of Z3's output.
export fn const_array sig dom s v -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, v~Value, r~Option Value
    match normal_const sig dom s v
        Some k -> Some (ArrayElem k)
        None   -> None

# The array Z3's `(store a j x)` is there.
export fn store_array sig dom s a j x -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, a~Value, j~Value, x~Value,
                                             r~Option Value
    match a
        ArrayElem k ->
            match normal_store sig dom s k j x
                Some l -> Some (ArrayElem l)
                None   -> None
        _           -> None

# The array Z3's `((_ map (+ (Int Int) Int)) a b)` is there.
export fn sum_array sig dom s a b -> r : sig~Sig, dom~(Nat -> List Sort -> Domain), s~Sort, a~Value, b~Value, r~Option Value
    match (a, b)
        (ArrayElem k, ArrayElem l) ->
            match normal_sum sig dom s k l
                Some n -> Some (ArrayElem n)
                None   -> None
        _                          -> None

# The element at `j` of the array `a` is there.
export fn select_array a j -> r : a~Value, j~Value, r~Option Value
    match a
        ArrayElem k -> normal_select k j
        _           -> None

# Kleene's `and` of two answers.
fn both p q -> r : p~Result Bool Unknown, q~Result Bool Unknown, r~Result Bool Unknown
    match (p, q)
        (Ok False, _)      -> Ok False
        (_, Ok False)      -> Ok False
        (Ok True, Ok True) -> Ok True
        (Err e, _)         -> Err e
        (_, Err e)         -> Err e

# ── Evaluation ───────────────────────────────────────────────────────────────

# How definitions are evaluated: `AsGiven`, by the model; `Unfolding`, each
# one marked terminating as its own body.
export enum Mode
    AsGiven
    Unfolding

# What evaluation at one level uses: `value`, evaluation one level down (a
# definition's body, in `Unfolding`).
record Lower
    value~(List (Result Value Unknown) -> List Sort -> Term -> Result Value Unknown)

# Evaluation `fuel` levels deep at most.
fn level mode c m fuel -> low : mode~Mode, c~Context, m~Model, fuel~Nat, low~Lower
    if fuel == 0
        Lower (\_ _ _ -> Err OutOfFuel)
    else
        Lower (\env senv t -> value (level mode c m (fuel - 1)) mode c m env senv t)

# The value of `t`, where `env` gives the values of its variables (`Var 0`
# first) and `senv` their sorts.
fn value low mode c m env senv t -> r : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                        senv~List Sort, t~Term, r~Result Value Unknown
    match t
        Var i          ->
            match list.head (list.drop i env)
                Some v -> v
                None   -> Err IllSorted
        App h args     -> apply low mode c m env senv t h args
        Let binds body ->
            # A `let` binds all its names at once, each in the outer
            # environment; it must bind at least one (`term.sort_of`).
            if binds == []
                Err IllSorted
            else
                match term.sorts_of (term.signature c) senv (term.bind_terms binds)
                    Ok ss -> value low mode c m (list.reverse (bound low mode c m env senv binds) ++ env) (list.reverse ss ++ senv) body
                    Err _ -> Err IllSorted
        # The array the model names for this `lambda` and the values of
        # the variables around it.
        Lam _ x body   ->
            let s = try sort_here c senv t
            let vs = try all_known env
            given_array c m s LambdaNotGiven (m.lambda s vs senv x body)

fn bound low mode c m env senv binds -> rs : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                             senv~List Sort, binds~List (Name, Term), rs~List (Result Value Unknown)
    match binds
        []             -> []
        (_, t) :: rest -> value low mode c m env senv t :: bound low mode c m env senv rest

fn values low mode c m env senv ts -> rs : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                           senv~List Sort, ts~List Term, rs~List (Result Value Unknown)
    match ts
        []        -> []
        t :: rest -> value low mode c m env senv t :: values low mode c m env senv rest

# Every result, if each is a value.
fn all_known rs -> r : rs~List (Result Value Unknown), r~Result (List Value) Unknown
    match rs
        []           -> Ok []
        Ok v :: rest ->
            let vs = try all_known rest
            Ok (v :: vs)
        Err e :: _   -> Err e

# The sort of `t` (whose head is applied here).
fn sort_here c senv t -> r : c~Context, senv~List Sort, t~Term, r~Result Sort Unknown
    match term.sort_of (term.signature c) senv t
        Ok s  -> Ok s
        Err _ -> Err IllSorted

# `h` applied to `args`; `t` is the whole application.
fn apply low mode c m env senv t h args -> r : low~Lower, mode~Mode, c~Context, m~Model,
                                               env~List (Result Value Unknown), senv~List Sort, t~Term, h~Head,
                                               args~List Term, r~Result Value Unknown
    match h
        Prim op    -> prim low mode c m env senv t op args
        Num n      -> Ok (Integer n)
        Boolean b  -> Ok (Truth b)
        EmptySeq _ -> Ok (Sequence [])
        ConstArr s ->
            match values low mode c m env senv args
                [v] ->
                    let x = try v
                    given_array c m s (NotGiven h) (m.const s x)
                _   -> Err IllSorted
        # The datatype `d` is not needed: a well-sorted term applies a
        # tester or selector only to values of its own datatype.
        Con _ k _  ->
            let vs = try all_known (values low mode c m env senv args)
            Ok (Constructed k vs)
        Is _ k     ->
            match values low mode c m env senv args
                [v] ->
                    match v
                        Ok (Constructed l _) -> Ok (Truth (k == l))
                        Ok _                 -> Err IllSorted
                        Err e                -> Err e
                _   -> Err IllSorted
        Sel d k j  ->
            match (args, values low mode c m env senv args)
                ([a], [v]) ->
                    match v
                        Ok (Constructed l fs) ->
                            if k == l
                                match list.head (list.drop j fs)
                                    Some x -> Ok x
                                    None   -> Err IllSorted
                            else
                                let s = try sort_here c senv a
                                let fs_sort = try sort_here c senv t
                                match s
                                    Data _ sargs -> given c m fs_sort h (m.wrong_sel d k j sargs (Constructed l fs))
                                    _            -> Err IllSorted
                        Ok _                  -> Err IllSorted
                        Err e                 -> Err e
                _          -> Err IllSorted
        Fun f      -> call low mode c m senv t f (values low mode c m env senv args)

# The definition of the `f`-th function, if it has one.
fn definition ds f -> r : ds~List (Nat, Def), f~Nat, r~Option Def
    match ds
        []             -> None
        (g, d) :: rest -> if g == f then Some d else definition rest f

# The `f`-th function at arguments `rs`.
fn call low mode c m senv t f rs -> r : low~Lower, mode~Mode, c~Context, m~Model, senv~List Sort, t~Term, f~Nat,
                                        rs~List (Result Value Unknown), r~Result Value Unknown
    match (mode, definition (term.defs c) f)
        (Unfolding, Some d) ->
            if unfolds d then low.value (list.reverse rs) (term.binder_env d.params) d.body else Err NotTerminating
        _                   ->
            let vs = try all_known rs
            let s = try sort_here c senv t
            given c m s (Fun f) (m.funs f vs)

fn as_bool r -> b : r~Result Value Unknown, b~Result Bool Unknown
    match r
        Ok (Truth x) -> Ok x
        Ok _         -> Err IllSorted
        Err e        -> Err e

fn as_int r -> n : r~Result Value Unknown, n~Result Int Unknown
    match r
        Ok (Integer x) -> Ok x
        Ok _           -> Err IllSorted
        Err e          -> Err e

fn truth r -> v : r~Result Bool Unknown, v~Result Value Unknown
    match r
        Ok b  -> Ok (Truth b)
        Err e -> Err e

# Kleene's `and` of `ts`, left to right, stopping at a definite `False`.
fn conj low mode c m env senv ts -> r : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                        senv~List Sort, ts~List Term, r~Result Bool Unknown
    match ts
        []        -> Ok True
        t :: rest ->
            match as_bool (value low mode c m env senv t)
                Ok False -> Ok False
                first    -> both first (conj low mode c m env senv rest)

# Kleene's `or` of `ts`, left to right, stopping at a definite `True`.
fn disj low mode c m env senv ts -> r : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                        senv~List Sort, ts~List Term, r~Result Bool Unknown
    match ts
        []        -> Ok False
        t :: rest ->
            match as_bool (value low mode c m env senv t)
                Ok True -> Ok True
                first   -> either first (disj low mode c m env senv rest)

# Kleene's `or` of two answers.
fn either p q -> r : p~Result Bool Unknown, q~Result Bool Unknown, r~Result Bool Unknown
    match (p, q)
        (Ok True, _)         -> Ok True
        (_, Ok True)         -> Ok True
        (Ok False, Ok False) -> Ok False
        (Err e, _)           -> Err e
        (_, Err e)           -> Err e

fn negate r -> s : r~Result Bool Unknown, s~Result Bool Unknown
    match r
        Ok b  -> Ok (not b)
        Err e -> Err e

# Integers `x` and `y`, both known, combined by `f`.
fn ints rx ry f -> r : rx~Result Value Unknown, ry~Result Value Unknown, f~(Int -> Int -> Result Value Unknown),
                       r~Result Value Unknown
    let x = try as_int rx
    let y = try as_int ry
    f x y

fn items r -> xs : r~Result Value Unknown, xs~Result (List Value) Unknown
    match r
        Ok (Sequence ys) -> Ok ys
        Ok _             -> Err IllSorted
        Err e            -> Err e

fn concat_all rs -> r : rs~List (Result Value Unknown), r~Result (List Value) Unknown
    match rs
        []        -> Ok []
        x :: rest ->
            let xs = try items x
            let ys = try concat_all rest
            Ok (xs ++ ys)

# The built-in operation `op` applied to `args`; `t` is the whole term.
fn prim low mode c m env senv t op args -> r : low~Lower, mode~Mode, c~Context, m~Model,
                                               env~List (Result Value Unknown), senv~List Sort, t~Term, op~Op,
                                               args~List Term, r~Result Value Unknown
    match (op, args)
        (Not, [a])              -> truth (negate (as_bool (value low mode c m env senv a)))
        (And, _)                -> truth (conj low mode c m env senv args)
        (Or, _)                 -> truth (disj low mode c m env senv args)
        (Implies, [a, b])       ->
            match as_bool (value low mode c m env senv a)
                Ok False -> Ok (Truth True)
                first    -> truth (either (negate first) (as_bool (value low mode c m env senv b)))
        (Ite, [p, a, b])        ->
            match as_bool (value low mode c m env senv p)
                Ok True  -> value low mode c m env senv a
                Ok False -> value low mode c m env senv b
                Err e    -> Err e
        (Eq, [a, b])            ->
            let x = try value low mode c m env senv a
            let y = try value low mode c m env senv b
            Ok (Truth (x == y))
        (Add, [a, b])           -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Integer (x + y)))
        (Sub, [a, b])           -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Integer (x - y)))
        (Mul, [a, b])           -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Integer (x * y)))
        (Neg, [a])              ->
            let x = try as_int (value low mode c m env senv a)
            Ok (Integer (0 - x))
        # Euclidean, as SMT-LIB's `Ints` theory defines `div` and `mod` (the
        # remainder is never negative), and as Checkers' `/` and `%` are. By
        # zero, they are what the model says.
        (Div, [a, b])           ->
            ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> if y != 0 then Ok (Integer (x / y)) else int_given (m.div_zero x) (Prim Div))
        (Mod, [a, b])           ->
            ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> if y != 0 then Ok (Integer (x % y)) else int_given (m.mod_zero x) (Prim Mod))
        (Lt, [a, b])            -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Truth (x < y)))
        (Le, [a, b])            -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Truth (x <= y)))
        (Gt, [a, b])            -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Truth (x > y)))
        (Ge, [a, b])            -> ints (value low mode c m env senv a) (value low mode c m env senv b) (\x y -> Ok (Truth (x >= y)))
        (Select, [a, i])        ->
            let x = try value low mode c m env senv a
            let j = try value low mode c m env senv i
            let s = try sort_here c senv a
            let w = try sort_here c senv t
            match x
                ArrayElem k -> given c m w (Prim Select) (m.select s k j)
                _           -> Err IllSorted
        (Store, [a, i, v])      ->
            let x = try value low mode c m env senv a
            let j = try value low mode c m env senv i
            let y = try value low mode c m env senv v
            let s = try sort_here c senv t
            match x
                ArrayElem k -> given_array c m s (NotGiven (Prim Store)) (m.store s k j y)
                _           -> Err IllSorted
        (MapAdd, [a, b])        ->
            let x = try value low mode c m env senv a
            let y = try value low mode c m env senv b
            let s = try sort_here c senv t
            match (x, y)
                (ArrayElem p, ArrayElem q) -> given_array c m s (NotGiven (Prim MapAdd)) (m.sum s p q)
                _                          -> Err IllSorted
        (SeqLen, [a])           ->
            let xs = try items (value low mode c m env senv a)
            Ok (Integer (list.length xs))
        # Inside the sequence, its element; outside, what the model says
        # (Z3 leaves `seq.nth` out of range unspecified).
        (SeqNth, [a, i])        ->
            let xs = try items (value low mode c m env senv a)
            let n = try as_int (value low mode c m env senv i)
            if 0 <= n and n < list.length xs
                match list.head (list.drop n xs)
                    Some x -> Ok x
                    None   -> Err IllSorted
            else
                let s = try sort_here c senv t
                given c m s (Prim SeqNth) (m.nth_out s xs n)
        (SeqUnit, [a])          ->
            let x = try value low mode c m env senv a
            Ok (Sequence [x])
        (SeqConcat, _)          ->
            let xs = try concat_all (values low mode c m env senv args)
            Ok (Sequence xs)
        # `n` elements from `i`, as many as there are; empty unless
        # `0 <= i < len` and `0 < n` (SMT-LIB's `str.substr`, and Z3's
        # `seq.extract`).
        (SeqExtract, [a, i, n]) ->
            let xs = try items (value low mode c m env senv a)
            let from = try as_int (value low mode c m env senv i)
            let count = try as_int (value low mode c m env senv n)
            if 0 <= from and from < list.length xs and 0 < count
                Ok (Sequence (list.take count (list.drop from xs)))
            else
                Ok (Sequence [])
        _                       -> Err IllSorted

fn int_given got h -> r : got~Option Int, h~Head, r~Result Value Unknown
    match got
        Some n -> Ok (Integer n)
        None   -> Err (NotGiven h)

# ── The meaning ──────────────────────────────────────────────────────────────

# The value of `t` in `m`, if `t` is a term of `c` without free variables
# (else `IllSorted`).
export fn eval c m t -> r : c~Context, m~Model, t~Term, r~Result Value Unknown
    if closed c t
        value (level AsGiven c m m.fuel) AsGiven c m [] [] t
    else
        Err IllSorted

# Whether `t` is a term of `c` without free variables: it has a sort there.
fn closed c t -> r : c~Context, t~Term, r~Bool
    match term.sort_of (term.signature c) [] t
        Ok _  -> True
        Err _ -> False

# Whether `t` is true in `m`.
export fn holds c m t -> r : c~Context, m~Model, t~Term, r~Bool
    eval c m t == Ok (Truth True)

# Whether `t` is false in `m`.
export fn fails c m t -> r : c~Context, m~Model, t~Term, r~Bool
    eval c m t == Ok (Truth False)

# Whether each of `ts` is true in `m`.
export fn holds_all c m ts -> r : c~Context, m~Model, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> holds c m t and holds_all c m rest

# Whether each of `vs` is a value of the sort in the same place of `ss`.
export fn values_of_sorts c m ss vs -> r : c~Context, m~Model, ss~List Sort, vs~List Value, r~Bool
    fields_of_sort c m ss vs

# Whether axiom `a` holds at the values `vs` of its variables, in order.
# Values that aren't of the variables' sorts in `m` are not among the ones
# `a` speaks of, so it holds at them: as a hypothesis ("`a` holds at all
# values") this asks nothing of them, and as a conclusion it says nothing
# about them. An axiom that isn't well-sorted in `c` (`term.axiom_ok`) holds
# nowhere.
export fn holds_at c m a vs -> r : c~Context, m~Model, a~Axiom, vs~List Value, r~Bool
    if not (term.axiom_ok c a)
        False
    else if values_of_sorts c m (term.var_sorts a.vars) vs
        value (level AsGiven c m m.fuel) AsGiven c m (list.reverse (list.map (\v -> Ok v) vs)) (term.binder_env a.vars) a.body
            == Ok (Truth True)
    else
        True

# The equation of definition `d`, the `n`-th function: for all values of
# its parameters, `(= (f x1 … xk) body)`. In the meaning a definition is
# this fact, so a model satisfies `d` when `holds_at` is true for it at all
# values.
export fn definition_axiom n d -> a : n~Nat, d~Def, a~Axiom
    let k = list.length d.params
    Axiom d.params (App (Prim Eq) [App (Fun n) (params_from k), d.body]) []

# `Var (k - 1)`, …, `Var 0`: the parameters of a binder list of `k`, in
# order (the last one bound is `Var 0`).
fn params_from k -> ts : k~Nat, ts~List Term
    if k == 0 then [] else Var (k - 1) :: params_from (k - 1)

# The value of `t` with each definition `refutes` may run (`unfolds`) run
# as its own body, if `t` is a term of `c` without free variables (else `IllSorted`).
export fn eval_unfolding c m t -> r : c~Context, m~Model, t~Term, r~Result Value Unknown
    if closed c t
        value (level Unfolding c m m.fuel) Unfolding c m [] [] t
    else
        Err IllSorted

# Whether `refutes` runs `d` as its own body: a `define-fun` (`Plain`)
# always, since its body applies only functions declared before it
# (`term.plain_bodies`); a recursive one only when marked terminating.
fn unfolds d -> r : d~Def, r~Bool
    match d.kind
        Plain     -> True
        Recursive -> d.terminates

# Whether `refutes` may run every definition of `c` (`unfolds`): every
# recursive one is marked terminating.
export fn defs_run c -> r : c~Context, r~Bool
    all_marked (term.defs c)

# Whether every recursive definition of `ds` is marked terminating.
fn all_marked ds -> r : ds~List (Nat, Def), r~Bool
    match ds
        []             -> True
        (_, d) :: rest -> unfolds d and all_marked rest

# Whether `t` has no `lambda` in it.
export fn lambda_free t -> r : t~Term, r~Bool
    match t
        Var _          -> True
        App _ args     -> all_lambda_free args
        Let binds body -> binds_lambda_free binds and lambda_free body
        Lam _ _ _      -> False

fn all_lambda_free ts -> r : ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> lambda_free t and all_lambda_free rest

fn binds_lambda_free bs -> r : bs~List (Name, Term), r~Bool
    match bs
        []             -> True
        (_, t) :: rest -> lambda_free t and binds_lambda_free rest

fn defs_lambda_free ds -> r : ds~List (Nat, Def), r~Bool
    match ds
        []             -> True
        (_, d) :: rest -> lambda_free d.body and defs_lambda_free rest

# Whether no fact or definition of `c`, nor `goal`, has a `lambda` in it.
export fn without_lambda c goal -> r : c~Context, goal~Term, r~Bool
    lambda_free goal and all_lambda_free (term.facts c) and defs_lambda_free (term.defs c)

# Whether `m` is a counterexample to `goal` in `c`. It asks that:
#
# - `goal` is a closed `Bool` term of `c` (`term.fact_ok`), and `c` has no
#   axioms (`term.axioms c == []`);
# - every recursive definition is marked terminating (`Def.terminates`,
#   which only the caller sets: `models --terminating` does, on its user's
#   word); a `define-fun` needs no mark (`unfolds`);
# - no fact, definition or the goal has a `lambda` in it;
# - each fact holds and the goal fails, in `normal_arrays m`, with each
#   definition run as its own body.
#
# What S6 proves of it (the `Invalid` theorem, in the header): when every
# recursive definition marked terminating does terminate, the
# interpretation `m` describes, with each definition its unique solution,
# satisfies every assertion of `c` and `not goal`. Its arrays are
# `normal_arrays`' normal forms, meant to be the same element exactly when
# they are the same function, so that it satisfies `arrays_ok` (owed by
# S6; `check`ed at points in `model_checks`). A `lambda` is refused because
# `normal_arrays` does not name one's array.
export fn refutes c goal m -> r : c~Context, goal~Term, m~Model, r~Bool
    let n = normal_arrays (term.signature c) m
    term.fact_ok c goal and term.axioms c == [] and defs_run c and without_lambda c goal
        and facts_hold_unfolding c n (term.facts c) and eval_unfolding c n goal == Ok (Truth False)

fn facts_hold_unfolding c m ts -> r : c~Context, m~Model, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> eval_unfolding c m t == Ok (Truth True) and facts_hold_unfolding c m rest

# ── What makes them SMT-LIB's arrays: `arrays_ok` ────────────────────────────
# At an array sort of the context (`array_sort`), a model's arrays are
# SMT-LIB's when, at all values of their arguments:
#
#     arrays_ok:    forall s a b i j x env senv xs body : …, model.arrays_ok_at c m s a b i j x env senv xs body
#     arrays_total: forall s a b i j x env senv xs body : …, model.arrays_total_at c m s a b i j x env senv xs body
#
# a theorem's named `forall` premises (SPEC §9.9), with the arguments'
# types: `s~Sort, a~Nat, b~Nat, i~Value, j~Value, x~Value, env~List Value,
# senv~List Sort, xs~Sort, body~Term`. `arrays_ok_at` is the laws:
# constant arrays, read over write, `map +`, `lambda`, extensionality;
# `arrays_total_at` says the model answers. Nothing in `eval` relies on
# them.
#
# **What a partial model owes.** A law asks nothing at a point where a read
# it needs isn't given (`None`), and nothing of arguments outside their
# sorts: there it is true. So a law is about what the model says, and
# `arrays_total` is the separate promise that it says everything.

# Whether `s` is an array sort of `c`.
export fn array_sort c s -> r : c~Context, s~Sort, r~Bool
    match s
        Arr _ _ -> term.sort_ok (term.signature c) 0 s
        _       -> False

# The laws at one point.
export fn arrays_ok_at c m s a b i j x env senv xs body -> r : c~Context, m~Model, s~Sort, a~Nat, b~Nat, i~Value,
                                                               j~Value, x~Value, env~List Value, senv~List Sort,
                                                               xs~Sort, body~Term, r~Bool
    const_law c m s x i and store_law c m s a j x i and sum_law c m s a b i and lambda_law c m s env senv xs body i
        and ext_law c m s a b

# What the model answers, at one point.
export fn arrays_total_at c m s a b i j x env senv xs body -> r : c~Context, m~Model, s~Sort, a~Nat, b~Nat, i~Value,
                                                                  j~Value, x~Value, env~List Value, senv~List Sort,
                                                                  xs~Sort, body~Term, r~Bool
    gives_select c m s a i and gives_const c m s x and gives_store c m s a j x and gives_sum c m s a b
        and gives_lambda c m s env senv xs body

# The laws at one point, but `lambda`'s.
export fn arrays_ok_but_lambda c m s a b i j x -> r : c~Context, m~Model, s~Sort, a~Nat, b~Nat, i~Value, j~Value,
                                                      x~Value, r~Bool
    const_law c m s x i and store_law c m s a j x i and sum_law c m s a b i and ext_law c m s a b

# What the model answers at one point, but `lambda`s.
export fn arrays_total_but_lambda c m s a b i j x -> r : c~Context, m~Model, s~Sort, a~Nat, b~Nat, i~Value, j~Value,
                                                         x~Value, r~Bool
    gives_select c m s a i and gives_const c m s x and gives_store c m s a j x and gives_sum c m s a b

# The laws and answers at one point are those but `lambda`'s, and
# `lambda`'s.
export lemma arrays_split c m s a b i j x env senv xs body : c~Context, m~Model, s~Sort, a~Nat, b~Nat, i~Value, j~Value,
                                                             x~Value, env~List Value, senv~List Sort, xs~Sort, body~Term
    ensures arrays_ok_at c m s a b i j x env senv xs body
            == (arrays_ok_but_lambda c m s a b i j x and lambda_law c m s env senv xs body i)
        and arrays_total_at c m s a b i j x env senv xs body
            == (arrays_total_but_lambda c m s a b i j x and gives_lambda c m s env senv xs body)

# Whether `k` is an array, `i` an index and `x` a value of array sort `s`
# of `c`.
fn sorted_at c m s k i x -> r : c~Context, m~Model, s~Sort, k~Nat, i~Value, x~Value, r~Bool
    match s
        Arr ix w -> array_sort c s and m.array_in s k and of_sort c m ix i and of_sort c m w x
        _        -> False

# Whether `i` is an index and `x` a value of array sort `s` of `c`.
fn index_and_value c m s i x -> r : c~Context, m~Model, s~Sort, i~Value, x~Value, r~Bool
    match s
        Arr ix w -> array_sort c s and of_sort c m ix i and of_sort c m w x
        _        -> False

# `select` answers at arrays and indices of their sorts, with a value of the
# element sort.
export fn gives_select c m s k i -> r : c~Context, m~Model, s~Sort, k~Nat, i~Value, r~Bool
    match s
        Arr ix w ->
            if array_sort c s and m.array_in s k and of_sort c m ix i
                match m.select s k i
                    Some v -> of_sort c m w v
                    None   -> False
            else
                True
        _        -> True

# The model names the constant array of `v`.
export fn gives_const c m s v -> r : c~Context, m~Model, s~Sort, v~Value, r~Bool
    match s
        Arr _ w -> if array_sort c s and of_sort c m w v then names_one m s (m.const s v) else True
        _       -> True

# The model names the store of `x` at `j` in `k`.
export fn gives_store c m s k j x -> r : c~Context, m~Model, s~Sort, k~Nat, j~Value, x~Value, r~Bool
    if sorted_at c m s k j x then names_one m s (m.store s k j x) else True

# The model names the sum of `a` and `b`, arrays of `Int`s.
export fn gives_sum c m s a b -> r : c~Context, m~Model, s~Sort, a~Nat, b~Nat, r~Bool
    match s
        Arr _ Int -> if array_sort c s and m.array_in s a and m.array_in s b then names_one m s (m.sum s a b) else True
        _         -> True

# Whether a `lambda` over a variable of sort `xs`, with body `body`, is a
# term of array sort `s` of `c` where the variables around it have sorts
# `senv` and values `env`.
fn lambda_sorted c m s env senv xs body -> r : c~Context, m~Model, s~Sort, env~List Value, senv~List Sort, xs~Sort,
                                               body~Term, r~Bool
    array_sort c s and term.sort_of (term.signature c) senv (Lam b"x" xs body) == Ok s
        and values_of_sorts c m (list.reverse senv) (list.reverse env)

# The model names the array of every `lambda` of sort `s`.
export fn gives_lambda c m s env senv xs body -> r : c~Context, m~Model, s~Sort, env~List Value, senv~List Sort, xs~Sort,
                                                     body~Term, r~Bool
    if lambda_sorted c m s env senv xs body then names_one m s (m.lambda s env senv xs body) else True

fn names_one m s got -> r : m~Model, s~Sort, got~Option Nat, r~Bool
    match got
        Some k -> m.array_in s k
        None   -> False

# A constant array is `x` at every index `i`.
export fn const_law c m s x i -> r : c~Context, m~Model, s~Sort, x~Value, i~Value, r~Bool
    if index_and_value c m s i x
        match m.const s x
            Some k ->
                m.array_in s k
                    and match m.select s k i
                        Some y -> y == x
                        None   -> True
            None   -> True
    else
        True

# Read over write: a store of `x` at `j` is `x` at `j`, and elsewhere what
# it was.
export fn store_law c m s k j x i -> r : c~Context, m~Model, s~Sort, k~Nat, j~Value, x~Value, i~Value, r~Bool
    if sorted_at c m s k j x and index_and_value c m s i x
        match m.store s k j x
            Some l -> m.array_in s l and same_where_given (m.select s l i) (if i == j then Some x else m.select s k i)
            None   -> True
    else
        True

# `map +` adds the two arrays at every index `i`.
export fn sum_law c m s a b i -> r : c~Context, m~Model, s~Sort, a~Nat, b~Nat, i~Value, r~Bool
    match s
        Arr _ Int ->
            if sorted_at c m s a i (Integer 0) and m.array_in s b
                match m.sum s a b
                    Some l ->
                        match (m.select s l i, m.select s a i, m.select s b i)
                            (Some (Integer p), Some (Integer q), Some (Integer r)) -> p == q + r
                            _                                                      -> True
                    None   -> True
            else
                True
        _         -> True

# A `lambda` is, at every index `i`, its body with the variable at `i`,
# wherever the body has a value there.
export fn lambda_law c m s env senv xs body i -> r : c~Context, m~Model, s~Sort, env~List Value, senv~List Sort,
                                                     xs~Sort, body~Term, i~Value, r~Bool
    if lambda_sorted c m s env senv xs body and of_sort c m xs i
        match m.lambda s env senv xs body
            Some k ->
                let at = Ok i :: list.map (\v -> Ok v) env
                match (value (level AsGiven c m m.fuel) AsGiven c m at (xs :: senv) body, m.select s k i)
                    (Ok v, Some y) -> y == v
                    _              -> True
            None   -> True
    else
        True

# Extensionality: two different arrays of `s` differ at the index `differ`
# gives. That index is of the index sort whatever `select` says there:
# `differ` always answers, so this asks no read the model may leave out,
# and were it allowed to give something else, no `select` would be asked
# and two arrays that read alike everywhere could be different.
export fn ext_law c m s a b -> r : c~Context, m~Model, s~Sort, a~Nat, b~Nat, r~Bool
    match s
        Arr ix _ ->
            if array_sort c s and a != b and m.array_in s a and m.array_in s b
                let i = m.differ s a b
                of_sort c m ix i
                    and match (m.select s a i, m.select s b i)
                        (Some p, Some q) -> p != q
                        _                -> True
            else
                True
        _        -> True

fn same_where_given p q -> r : p~Option Value, q~Option Value, r~Bool
    match (p, q)
        (Some x, Some y) -> x == y
        _                -> True

# ── The meaning of a connective ──────────────────────────────────────────────
# What the certificate checker (`smt.cert`) relies on: a term's value is
# that of the connective `term.structure` sees in it, through `let`.

# The connective `s` of `t`, as a term (`t` itself for an atom).
fn connective_term t s -> r : t~Term, s~Connective, r~Term
    match s
        Atom          -> t
        ConstOf b     -> App (Boolean b) []
        NotOf a       -> App (Prim Not) [a]
        AndOf ps      -> App (Prim And) ps
        OrOf ps       -> App (Prim Or) ps
        ImpliesOf a b -> App (Prim Implies) [a, b]
        IteOf p a b   -> App (Prim Ite) [p, a, b]
        IffOf a b     -> App (Prim Eq) [a, b]

# Whether `Let binds` evaluates its body here: it binds something, and
# what it binds has sorts.
fn binds_ok c senv binds -> r : c~Context, senv~List Sort, binds~List (Name, Term), r~Bool
    if binds == []
        False
    else
        match term.sorts_of (term.signature c) senv (term.bind_terms binds)
            Ok _  -> True
            Err _ -> False

# The environment the body of `Let binds` is evaluated in, and its sorts.
fn inner_env low mode c m env senv binds -> e : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                                senv~List Sort, binds~List (Name, Term), e~List (Result Value Unknown)
    list.reverse (bound low mode c m env senv binds) ++ env

fn inner_sorts c senv binds -> e : c~Context, senv~List Sort, binds~List (Name, Term), e~List Sort
    match term.sorts_of (term.signature c) senv (term.bind_terms binds)
        Ok ss -> list.reverse ss ++ senv
        Err _ -> senv

lemma let_value low mode c m env senv binds t : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                                senv~List Sort, binds~List (Name, Term), t~Term
    ensures value low mode c m env senv (Let binds t)
        == (if binds_ok c senv binds then value low mode c m (inner_env low mode c m env senv binds) (inner_sorts c senv binds) t else Err IllSorted)
    proof
        auto

lemma conj_under low mode c m env senv binds ps : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                                  senv~List Sort, binds~List (Name, Term), ps~List Term, binds_ok c senv binds
    ensures conj low mode c m env senv (list.map (\p -> Let binds p) ps)
        == conj low mode c m (inner_env low mode c m env senv binds) (inner_sorts c senv binds) ps
    proof
        match ps
            []        -> auto
            p :: rest ->
                have let_value low mode c m env senv binds p
                have conj_under low mode c m env senv binds rest

lemma conj_not_ok low mode c m env senv binds ps : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                                   senv~List Sort, binds~List (Name, Term), ps~List Term, ps != [],
                                                   not (binds_ok c senv binds)
    ensures conj low mode c m env senv (list.map (\p -> Let binds p) ps) == Err IllSorted
    proof
        match ps
            p :: rest ->
                have let_value low mode c m env senv binds p
                if rest != []
                    have conj_not_ok low mode c m env senv binds rest
                else
                    auto

lemma disj_under low mode c m env senv binds ps : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                                  senv~List Sort, binds~List (Name, Term), ps~List Term, binds_ok c senv binds
    ensures disj low mode c m env senv (list.map (\p -> Let binds p) ps)
        == disj low mode c m (inner_env low mode c m env senv binds) (inner_sorts c senv binds) ps
    proof
        match ps
            []        -> auto
            p :: rest ->
                have let_value low mode c m env senv binds p
                have disj_under low mode c m env senv binds rest

lemma disj_not_ok low mode c m env senv binds ps : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                                   senv~List Sort, binds~List (Name, Term), ps~List Term, ps != [],
                                                   not (binds_ok c senv binds)
    ensures disj low mode c m env senv (list.map (\p -> Let binds p) ps) == Err IllSorted
    proof
        match ps
            p :: rest ->
                have let_value low mode c m env senv binds p
                if rest != []
                    have disj_not_ok low mode c m env senv binds rest
                else
                    auto

# A conjunction or disjunction `term.structure` sees has parts.
lemma parts_nonempty t ps : t~Term, ps~List Term
    ensures (term.structure t == AndOf ps or term.structure t == OrOf ps) implies ps != []
    proof
        match t
            Let binds body ->
                match term.structure body
                    AndOf qs -> have parts_nonempty body qs
                    OrOf qs  -> have parts_nonempty body qs
                    _        -> auto
            _              -> auto

lemma structure_value low mode c m env senv t : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                                senv~List Sort, t~Term
    ensures value low mode c m env senv t == value low mode c m env senv (connective_term t (term.structure t))
    proof
        match t
            Let binds body ->
                let inner = inner_env low mode c m env senv binds
                let sorts = inner_sorts c senv binds
                have let_value low mode c m env senv binds body
                have structure_value low mode c m inner sorts body
                match term.structure body
                    AndOf ps      ->
                        have parts_nonempty body ps
                        if binds_ok c senv binds
                            have conj_under low mode c m env senv binds ps
                        else
                            have conj_not_ok low mode c m env senv binds ps
                    OrOf ps       ->
                        have parts_nonempty body ps
                        if binds_ok c senv binds
                            have disj_under low mode c m env senv binds ps
                        else
                            have disj_not_ok low mode c m env senv binds ps
                    NotOf a       -> have let_value low mode c m env senv binds a
                    ImpliesOf a b ->
                        have let_value low mode c m env senv binds a
                        have let_value low mode c m env senv binds b
                    IteOf p a b   ->
                        have let_value low mode c m env senv binds p
                        have let_value low mode c m env senv binds a
                        have let_value low mode c m env senv binds b
                    IffOf a b     ->
                        have let_value low mode c m env senv binds a
                        have let_value low mode c m env senv binds b
                    _             -> auto
            _              -> auto

# ── What a connective means, for closed terms ────────────────────────────────

# Whether `t` is a closed `Bool` term of `c`.
export transparent fn boolean c t -> r : c~Context, t~Term, r~Bool
    term.sort_of (term.signature c) [] t == Ok Bool

# Whether each of `ts` is (`boolean`).
export transparent fn booleans c ts -> r : c~Context, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> boolean c t and booleans c rest

# ── Every function of the model answers: `total` ─────────────────────────────
# A model is total when it answers every question an interpretation answers:
# what its functions give, and what SMT-LIB leaves unspecified. A question
# is a `Read`, and `gives c m r` says that `m` answers `r` with a value of
# the sort needed. A theorem asks it as a named `forall` premise (SPEC
# §9.9), at every read:
#
#     total: forall r : r~Read, model.gives c m r
#
# A narrower shape asks it only at the reads of a finite set of terms
# (`rs`, a `List Read`):
#
#     total: forall r : r~Read, list.contains rs r, model.gives c m r
#
# No theorem uses that shape yet. `rs` would depend on the model as well
# as the terms: a `FunAt f vs` carries the values of `f`'s arguments in
# `m`, so for a theorem about every `m` it is a function of `m` and the
# terms, not a list fixed beforehand.
#
# The arrays' reads (`select`, `const`, `store`, `map +`, `lambda`) are not
# here: `arrays_total_at` says the model answers them, with the laws.
#
# Each is what an SMT-LIB structure gives (2.6, §5.3), or for `seq.nth`
# what Z3 gives, and asks nothing of arguments outside their sorts, where
# it is true:
#
# - `FunAt f vs`: the `f`-th function is total on its parameters' sorts,
#   with a value of its result sort (Definition 6);
# - `DivZeroAt n`, `ModZeroAt n`: `div` and `mod` are total on `Int`, and
#   at divisor 0 a function of `n` (the theory `Ints`);
# - `NthOutAt e xs i`: Z3's `seq.nth` is total, outside the sequence a
#   function of `xs` and `i` of sort `e`;
# - `WrongSelAt d k j args v`: a selector is a total function on its
#   datatype (Definition 6), at a value another constructor built
#   constrained only to be of the field's sort (Remark 11, p. 78).

# A question a model answers: see the section's comment.
export enum Read
    FunAt f vs              : f~Nat, vs~List Value
    DivZeroAt n             : n~Int
    ModZeroAt n             : n~Int
    NthOutAt e xs i         : e~Sort, xs~List Value, i~Int
    WrongSelAt d k j args v : d~Nat, k~Nat, j~Nat, args~List Sort, v~Value

# Whether `m` answers `r`, with a value of the sort needed, where its
# arguments are of their sorts in `c`.
export fn gives c m r -> b : c~Context, m~Model, r~Read, b~Bool
    match r
        FunAt f vs              -> gives_fun c m f vs
        DivZeroAt n             -> m.div_zero n != None
        ModZeroAt n             -> m.mod_zero n != None
        NthOutAt e xs i         -> gives_nth_out c m e xs i
        WrongSelAt d k j args v -> gives_wrong_sel c m d k j args v

# The `f`-th function answers at values `vs` of its parameters' sorts.
fn gives_fun c m f vs -> r : c~Context, m~Model, f~Nat, vs~List Value, r~Bool
    let sig = term.signature c
    if f < len sig.funs and values_of_sorts c m sig.funs[f].params vs
        answers_with c m sig.funs[f].result (m.funs f vs)
    else
        True

# `(seq.nth xs i)` for `xs` of elements of sort `e` and `i` outside it.
fn gives_nth_out c m e xs i -> r : c~Context, m~Model, e~Sort, xs~List Value, i~Int, r~Bool
    if term.sort_ok (term.signature c) 0 e and all_of_sort c m e xs and not (0 <= i and i < list.length xs)
        answers_with c m e (m.nth_out e xs i)
    else
        True

# Selector `j` of constructor `k` of `(d args)` at a value `v` of that
# sort built by another constructor.
fn gives_wrong_sel c m d k j args v -> r : c~Context, m~Model, d~Nat, k~Nat, j~Nat, args~List Sort, v~Value, r~Bool
    let sig = term.signature c
    if term.sort_ok sig 0 (Data d args) and of_sort c m (Data d args) v and not (built_by k v)
        match term.ctor sig d k
            Some kc ->
                match list.head (list.drop j kc.fields)
                    Some fd -> answers_with c m (term.instantiate args fd.sort) (m.wrong_sel d k j args v)
                    None    -> True
            None    -> True
    else
        True

fn built_by k v -> r : k~Nat, v~Value, r~Bool
    match v
        Constructed l _ -> l == k
        _               -> False

fn answers_with c m s got -> r : c~Context, m~Model, s~Sort, got~Option Value, r~Bool
    match got
        Some v -> of_sort c m s v
        None   -> False

# Whether `t` has a value of its sort in `m`.
export fn has_value c m t -> r : c~Context, m~Model, t~Term, r~Bool
    match (term.sort_of (term.signature c) [] t, eval c m t)
        (Ok s, Ok v) -> of_sort c m s v
        _            -> False

# Whether some of `ts` is true in `m`.
export transparent fn holds_one c m ts -> r : c~Context, m~Model, ts~List Term, r~Bool
    match ts
        []        -> False
        t :: rest -> holds c m t or holds_one c m rest

# Whether each of `ts` is false in `m`.
export transparent fn fails_all c m ts -> r : c~Context, m~Model, ts~List Term, r~Bool
    match ts
        []        -> True
        t :: rest -> fails c m t and fails_all c m rest

# Whether some of `ts` is false in `m`.
export transparent fn fails_one c m ts -> r : c~Context, m~Model, ts~List Term, r~Bool
    match ts
        []        -> False
        t :: rest -> fails c m t or fails_one c m rest

export lemma holds_all_nil c m : c~Context, m~Model
    ensures holds_all c m []

export lemma holds_all_cons c m t ts : c~Context, m~Model, t~Term, ts~List Term
    ensures holds_all c m (t :: ts) == (holds c m t and holds_all c m ts)

# A term is never both true and false.
export lemma not_both c m t : c~Context, m~Model, t~Term
    ensures not (holds c m t and fails c m t)

# A closed `Bool` term with a value is true or false.
export lemma two_valued c m t : c~Context, m~Model, t~Term, boolean c t, has_value c m t
    ensures holds c m t or fails c m t
    proof
        have holds_is c m t
        match eval c m t
            Ok v  ->
                have of_sort c m Bool v
                match v
                    Truth _ -> auto
                    _       -> auto
            Err _ -> auto

# `ite`'s value: `x` if `r` is true, `y` if false.
fn choose r x y -> v : r~Result Bool Unknown, x~Result Value Unknown, y~Result Value Unknown, v~Result Value Unknown
    match r
        Ok True  -> x
        Ok False -> y
        Err e    -> Err e

# `=`'s value.
fn equal x y -> v : x~Result Value Unknown, y~Result Value Unknown, v~Result Value Unknown
    match (x, y)
        (Ok a, Ok b) -> Ok (Truth (a == b))
        (Err e, _)   -> Err e
        (_, Err e)   -> Err e

# One step of evaluation, for any `low`.
lemma app_value low mode c m env senv h args : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                               senv~List Sort, h~Head, args~List Term
    ensures value low mode c m env senv (App h args) == apply low mode c m env senv (App h args) h args

lemma not_value low mode c m env senv a : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                          senv~List Sort, a~Term
    ensures value low mode c m env senv (App (Prim Not) [a]) == truth (negate (as_bool (value low mode c m env senv a)))
    proof
        have app_value low mode c m env senv (Prim Not) [a]

lemma and_value low mode c m env senv ps : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                           senv~List Sort, ps~List Term
    ensures value low mode c m env senv (App (Prim And) ps) == truth (conj low mode c m env senv ps)
    proof
        have app_value low mode c m env senv (Prim And) ps

lemma or_value low mode c m env senv ps : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                          senv~List Sort, ps~List Term
    ensures value low mode c m env senv (App (Prim Or) ps) == truth (disj low mode c m env senv ps)
    proof
        have app_value low mode c m env senv (Prim Or) ps

lemma implies_value low mode c m env senv a b : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                                senv~List Sort, a~Term, b~Term
    ensures value low mode c m env senv (App (Prim Implies) [a, b])
        == (if as_bool (value low mode c m env senv a) == Ok False then Ok (Truth True) else truth (either (negate (as_bool (value low mode c m env senv a))) (as_bool (value low mode c m env senv b))))
    proof
        have app_value low mode c m env senv (Prim Implies) [a, b]

lemma ite_value low mode c m env senv p a b : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                              senv~List Sort, p~Term, a~Term, b~Term
    ensures value low mode c m env senv (App (Prim Ite) [p, a, b])
        == choose (as_bool (value low mode c m env senv p)) (value low mode c m env senv a) (value low mode c m env senv b)
    proof
        have app_value low mode c m env senv (Prim Ite) [p, a, b]

lemma eq_value low mode c m env senv a b : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                           senv~List Sort, a~Term, b~Term
    ensures value low mode c m env senv (App (Prim Eq) [a, b])
        == equal (value low mode c m env senv a) (value low mode c m env senv b)
    proof
        have app_value low mode c m env senv (Prim Eq) [a, b]

lemma conj_cons low mode c m env senv p ps : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                             senv~List Sort, p~Term, ps~List Term
    ensures conj low mode c m env senv (p :: ps)
        == (if as_bool (value low mode c m env senv p) == Ok False then Ok False else both (as_bool (value low mode c m env senv p)) (conj low mode c m env senv ps))

lemma disj_cons low mode c m env senv p ps : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                             senv~List Sort, p~Term, ps~List Term
    ensures disj low mode c m env senv (p :: ps)
        == (if as_bool (value low mode c m env senv p) == Ok True then Ok True else either (as_bool (value low mode c m env senv p)) (disj low mode c m env senv ps))

# Each connective's value, for any `low`: what `structure_value` and one
# step of evaluation give.
lemma const_structure low mode c m env senv t b : low~Lower, mode~Mode, c~Context, m~Model,
                                                  env~List (Result Value Unknown), senv~List Sort, t~Term, b~Bool,
                                                  term.structure t == ConstOf b
    ensures value low mode c m env senv t == Ok (Truth b)
    proof
        have structure_value low mode c m env senv t
        have app_value low mode c m env senv (Boolean b) []

lemma not_structure low mode c m env senv t a : low~Lower, mode~Mode, c~Context, m~Model,
                                                env~List (Result Value Unknown), senv~List Sort, t~Term, a~Term,
                                                term.structure t == NotOf a
    ensures value low mode c m env senv t == truth (negate (as_bool (value low mode c m env senv a)))
    proof
        have structure_value low mode c m env senv t
        have not_value low mode c m env senv a

lemma and_structure low mode c m env senv t ps : low~Lower, mode~Mode, c~Context, m~Model,
                                                 env~List (Result Value Unknown), senv~List Sort, t~Term, ps~List Term,
                                                 term.structure t == AndOf ps
    ensures value low mode c m env senv t == truth (conj low mode c m env senv ps)
    proof
        have structure_value low mode c m env senv t
        have and_value low mode c m env senv ps

lemma or_structure low mode c m env senv t ps : low~Lower, mode~Mode, c~Context, m~Model,
                                                env~List (Result Value Unknown), senv~List Sort, t~Term, ps~List Term,
                                                term.structure t == OrOf ps
    ensures value low mode c m env senv t == truth (disj low mode c m env senv ps)
    proof
        have structure_value low mode c m env senv t
        have or_value low mode c m env senv ps

lemma implies_structure low mode c m env senv t a b : low~Lower, mode~Mode, c~Context, m~Model,
                                                      env~List (Result Value Unknown), senv~List Sort, t~Term, a~Term,
                                                      b~Term, term.structure t == ImpliesOf a b
    ensures value low mode c m env senv t
        == (if as_bool (value low mode c m env senv a) == Ok False then Ok (Truth True) else truth (either (negate (as_bool (value low mode c m env senv a))) (as_bool (value low mode c m env senv b))))
    proof
        have structure_value low mode c m env senv t
        have implies_value low mode c m env senv a b

lemma ite_structure low mode c m env senv t p a b : low~Lower, mode~Mode, c~Context, m~Model,
                                                    env~List (Result Value Unknown), senv~List Sort, t~Term, p~Term, a~Term,
                                                    b~Term, term.structure t == IteOf p a b
    ensures value low mode c m env senv t
        == choose (as_bool (value low mode c m env senv p)) (value low mode c m env senv a) (value low mode c m env senv b)
    proof
        have structure_value low mode c m env senv t
        have ite_value low mode c m env senv p a b

lemma iff_structure low mode c m env senv t a b : low~Lower, mode~Mode, c~Context, m~Model,
                                                  env~List (Result Value Unknown), senv~List Sort, t~Term, a~Term, b~Term,
                                                  term.structure t == IffOf a b
    ensures value low mode c m env senv t == equal (value low mode c m env senv a) (value low mode c m env senv b)
    proof
        have structure_value low mode c m env senv t
        have eq_value low mode c m env senv a b

# Kleene's `and` of a list, one part at a time, for any `low`.
lemma conj_step low mode c m env senv p ps : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                             senv~List Sort, p~Term, ps~List Term
    ensures (conj low mode c m env senv (p :: ps) == Ok True)
            == (value low mode c m env senv p == Ok (Truth True) and conj low mode c m env senv ps == Ok True)
        and (value low mode c m env senv p == Ok (Truth False) implies conj low mode c m env senv (p :: ps) == Ok False)
        and (conj low mode c m env senv ps == Ok False implies conj low mode c m env senv (p :: ps) == Ok False)
    proof
        have conj_cons low mode c m env senv p ps

lemma disj_step low mode c m env senv p ps : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                             senv~List Sort, p~Term, ps~List Term
    ensures (disj low mode c m env senv (p :: ps) == Ok False)
            == (value low mode c m env senv p == Ok (Truth False) and disj low mode c m env senv ps == Ok False)
        and (value low mode c m env senv p == Ok (Truth True) implies disj low mode c m env senv (p :: ps) == Ok True)
        and (disj low mode c m env senv ps == Ok True implies disj low mode c m env senv (p :: ps) == Ok True)
    proof
        have disj_cons low mode c m env senv p ps

lemma conj_nil low mode c m env senv : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                       senv~List Sort
    ensures conj low mode c m env senv [] == Ok True

lemma disj_nil low mode c m env senv : low~Lower, mode~Mode, c~Context, m~Model, env~List (Result Value Unknown),
                                       senv~List Sort
    ensures disj low mode c m env senv [] == Ok False

# `eval` of a closed term: its value at the top level, with no variables.
lemma eval_closed c m t : c~Context, m~Model, t~Term, boolean c t
    ensures eval c m t == value (level AsGiven c m m.fuel) AsGiven c m [] [] t

export lemma holds_is c m t : c~Context, m~Model, t~Term
    ensures holds c m t == (eval c m t == Ok (Truth True)) and fails c m t == (eval c m t == Ok (Truth False))

# What `truth`, `negate`, `as_bool`, `either`, `choose` and `equal` give
# at Booleans.
lemma truth_of r : r~Result Bool Unknown
    ensures (truth r == Ok (Truth True)) == (r == Ok True) and (truth r == Ok (Truth False)) == (r == Ok False)

lemma bool_of r : r~Result Value Unknown
    ensures (as_bool r == Ok True) == (r == Ok (Truth True)) and (as_bool r == Ok False) == (r == Ok (Truth False))
        and (negate (as_bool r) == Ok True) == (r == Ok (Truth False))
        and (negate (as_bool r) == Ok False) == (r == Ok (Truth True))

lemma either_of p q : p~Result Bool Unknown, q~Result Bool Unknown
    ensures (p == Ok True implies either p q == Ok True) and (q == Ok True implies either p q == Ok True)
        and (p == Ok False and q == Ok False implies either p q == Ok False)

lemma choose_of r x y : r~Result Bool Unknown, x~Result Value Unknown, y~Result Value Unknown
    ensures (r == Ok True implies choose r x y == x) and (r == Ok False implies choose r x y == y)

lemma equal_of x y : x~Result Value Unknown, y~Result Value Unknown
    ensures (x == Ok (Truth True) and y == Ok (Truth True) implies equal x y == Ok (Truth True))
        and (x == Ok (Truth False) and y == Ok (Truth False) implies equal x y == Ok (Truth True))
        and (x == Ok (Truth True) and y == Ok (Truth False) implies equal x y == Ok (Truth False))
        and (x == Ok (Truth False) and y == Ok (Truth True) implies equal x y == Ok (Truth False))

export lemma const_meaning c m t b : c~Context, m~Model, t~Term, b~Bool, boolean c t, term.structure t == ConstOf b
    ensures eval c m t == Ok (Truth b)
    proof
        have eval_closed c m t
        have const_structure (level AsGiven c m m.fuel) AsGiven c m [] [] t b

export lemma not_meaning c m t a : c~Context, m~Model, t~Term, a~Term, boolean c t, boolean c a, term.structure t == NotOf a
    ensures holds c m t == fails c m a and fails c m t == holds c m a
    proof
        let low = level AsGiven c m m.fuel
        have eval_closed c m t
        have eval_closed c m a
        have holds_is c m t
        have holds_is c m a
        have not_structure low AsGiven c m [] [] t a
        have truth_of (negate (as_bool (value low AsGiven c m [] [] a)))
        have bool_of (value low AsGiven c m [] [] a)

lemma conj_closed c m ps : c~Context, m~Model, ps~List Term, booleans c ps
    ensures (conj (level AsGiven c m m.fuel) AsGiven c m [] [] ps == Ok True) == holds_all c m ps
        and (fails_one c m ps implies conj (level AsGiven c m m.fuel) AsGiven c m [] [] ps == Ok False)
    proof
        let low = level AsGiven c m m.fuel
        match ps
            []        ->
                have conj_nil low AsGiven c m [] []
                have holds_all_nil c m
            p :: rest ->
                have eval_closed c m p
                have holds_is c m p
                have holds_all_cons c m p rest
                have fails_one c m ps == (fails c m p or fails_one c m rest)
                have conj_step low AsGiven c m [] [] p rest
                have conj_closed c m rest

lemma disj_closed c m ps : c~Context, m~Model, ps~List Term, booleans c ps
    ensures (disj (level AsGiven c m m.fuel) AsGiven c m [] [] ps == Ok False) == fails_all c m ps
        and (holds_one c m ps implies disj (level AsGiven c m m.fuel) AsGiven c m [] [] ps == Ok True)
    proof
        let low = level AsGiven c m m.fuel
        match ps
            []        -> have disj_nil low AsGiven c m [] []
            p :: rest ->
                have eval_closed c m p
                have holds_is c m p
                have disj_step low AsGiven c m [] [] p rest
                have disj_closed c m rest

export lemma and_meaning c m t ps : c~Context, m~Model, t~Term, ps~List Term, boolean c t, booleans c ps,
                                    term.structure t == AndOf ps
    ensures holds c m t == holds_all c m ps and (fails_one c m ps implies fails c m t)
    proof
        let low = level AsGiven c m m.fuel
        have eval_closed c m t
        have holds_is c m t
        have and_structure low AsGiven c m [] [] t ps
        have truth_of (conj low AsGiven c m [] [] ps)
        have conj_closed c m ps

export lemma or_meaning c m t ps : c~Context, m~Model, t~Term, ps~List Term, boolean c t, booleans c ps,
                                   term.structure t == OrOf ps
    ensures fails c m t == fails_all c m ps and (holds_one c m ps implies holds c m t)
    proof
        let low = level AsGiven c m m.fuel
        have eval_closed c m t
        have holds_is c m t
        have or_structure low AsGiven c m [] [] t ps
        have truth_of (disj low AsGiven c m [] [] ps)
        have disj_closed c m ps

export lemma implies_meaning c m t a b : c~Context, m~Model, t~Term, a~Term, b~Term, boolean c t, boolean c a, boolean c b,
                                         term.structure t == ImpliesOf a b
    ensures (fails c m a implies holds c m t) and (holds c m b implies holds c m t)
        and (holds c m a and fails c m b implies fails c m t)
    proof
        let low = level AsGiven c m m.fuel
        let va = value low AsGiven c m [] [] a
        let vb = value low AsGiven c m [] [] b
        have eval_closed c m t
        have eval_closed c m a
        have eval_closed c m b
        have holds_is c m t
        have holds_is c m a
        have holds_is c m b
        have implies_structure low AsGiven c m [] [] t a b
        have bool_of va
        have bool_of vb
        have either_of (negate (as_bool va)) (as_bool vb)
        have truth_of (either (negate (as_bool va)) (as_bool vb))

export lemma ite_meaning c m t p a b : c~Context, m~Model, t~Term, p~Term, a~Term, b~Term, boolean c t, boolean c p,
                                       boolean c a, boolean c b, term.structure t == IteOf p a b
    ensures (holds c m p implies eval c m t == eval c m a) and (fails c m p implies eval c m t == eval c m b)
    proof
        let low = level AsGiven c m m.fuel
        let vp = value low AsGiven c m [] [] p
        have eval_closed c m t
        have eval_closed c m p
        have eval_closed c m a
        have eval_closed c m b
        have holds_is c m p
        have ite_structure low AsGiven c m [] [] t p a b
        have bool_of vp
        have choose_of (as_bool vp) (value low AsGiven c m [] [] a) (value low AsGiven c m [] [] b)

export lemma iff_meaning c m t a b : c~Context, m~Model, t~Term, a~Term, b~Term, boolean c t, boolean c a, boolean c b,
                                     term.structure t == IffOf a b
    ensures (holds c m a and holds c m b implies holds c m t) and (fails c m a and fails c m b implies holds c m t)
        and (holds c m a and fails c m b implies fails c m t) and (fails c m a and holds c m b implies fails c m t)
    proof
        let low = level AsGiven c m m.fuel
        have eval_closed c m t
        have eval_closed c m a
        have eval_closed c m b
        have holds_is c m t
        have holds_is c m a
        have holds_is c m b
        have iff_structure low AsGiven c m [] [] t a b
        have equal_of (value low AsGiven c m [] [] a) (value low AsGiven c m [] [] b)

# ── The meaning doesn't use fuel ─────────────────────────────────────────────
# `Model.fuel` bounds how deep `refutes` unfolds definitions. The meaning
# (`eval`, `holds`, `fails`, `holds_all`, `holds_at`) unfolds none, so its
# answers are the same whatever the fuel: `eval_fuel`, `holds_fuel`,
# `fails_fuel`, `holds_all_fuel`, `holds_at_fuel`, `has_value_fuel`; and so
# are the premises a theorem takes of a model: `gives_fuel`,
# `arrays_ok_at_fuel`, `arrays_total_at_fuel`. `with_fuel` is transparent,
# so a model written out field by field is one of these.

# `m` with `n` levels of fuel.
export transparent fn with_fuel m n -> r : m~Model, n~Nat, r~Model
    Model m.funs m.select m.const m.store m.sum m.lambda m.array_in m.differ m.div_zero m.mod_zero m.nth_out m.wrong_sel m.domain n

lemma of_sort_fuel c m n s v : c~Context, m~Model, n~Nat, s~Sort, v~Value
    ensures of_sort c m s v == of_sort c (with_fuel m n) s v
    proof
        match (s, v)
            (Seq e, Sequence xs)            -> have all_of_sort_fuel c m n e xs
            (Data d args, Constructed k fs) ->
                match term.ctor (term.signature c) d k
                    Some kc -> have fields_of_sort_fuel c m n (list.map (term.instantiate args) (term.field_sorts kc.fields)) fs
                    None    -> auto
            _                               -> auto

lemma all_of_sort_fuel c m n s vs : c~Context, m~Model, n~Nat, s~Sort, vs~List Value
    ensures all_of_sort c m s vs == all_of_sort c (with_fuel m n) s vs
    proof
        match vs
            []        -> auto
            v :: rest ->
                have of_sort_fuel c m n s v
                have all_of_sort_fuel c m n s rest

lemma fields_of_sort_fuel c m n ss vs : c~Context, m~Model, n~Nat, ss~List Sort, vs~List Value
    ensures fields_of_sort c m ss vs == fields_of_sort c (with_fuel m n) ss vs
    proof
        match (ss, vs)
            (s :: sr, v :: vr) ->
                have of_sort_fuel c m n s v
                have fields_of_sort_fuel c m n sr vr
            _                  -> auto

lemma sorts_fuel c m n : c~Context, m~Model, n~Nat
    ensures forall s v : s~Sort, v~Value, of_sort c m s v == of_sort c (with_fuel m n) s v
    proof
        have of_sort_fuel c m n s v

lemma given_at c m n s h got : c~Context, m~Model, n~Nat, s~Sort, h~Head, got~Option Value
    ensures given c m s h got == given c (with_fuel m n) s h got
    proof
        match got
            Some v -> have of_sort_fuel c m n s v
            None   -> auto

lemma given_fuel c m n : c~Context, m~Model, n~Nat
    ensures forall s h got : s~Sort, h~Head, got~Option Value, given c m s h got == given c (with_fuel m n) s h got
    proof
        match got
            Some v -> have of_sort_fuel c m n s v
            None   -> auto

lemma value_fuel low low2 c m n env senv t : low~Lower, low2~Lower, c~Context, m~Model, n~Nat,
                                             env~List (Result Value Unknown), senv~List Sort, t~Term
    ensures value low AsGiven c m env senv t == value low2 AsGiven c (with_fuel m n) env senv t
    proof
        have sorts_fuel c m n
        match t
            App h args     -> have apply_fuel low low2 c m n env senv t h args
            Let binds body ->
                match term.sorts_of (term.signature c) senv (term.bind_terms binds)
                    Ok ss ->
                        have bound_fuel low low2 c m n env senv binds
                        let inner = list.reverse (bound low AsGiven c m env senv binds) ++ env
                        have value_fuel low low2 c m n inner (list.reverse ss ++ senv) body
                    Err _ -> auto
            _              -> auto

lemma apply_fuel low low2 c m n env senv t h args : low~Lower, low2~Lower, c~Context, m~Model, n~Nat,
                                                    env~List (Result Value Unknown), senv~List Sort, t~Term, h~Head,
                                                    args~List Term
    ensures apply low AsGiven c m env senv t h args == apply low2 AsGiven c (with_fuel m n) env senv t h args
    proof
        have given_fuel c m n
        have values_fuel low low2 c m n env senv args
        match h
            Prim op    -> have prim_fuel low low2 c m n env senv t op args
            Num _      -> auto
            Boolean _  -> auto
            EmptySeq _ -> auto
            ConstArr _ -> auto
            Con _ _ _  -> auto
            Is _ _     -> auto
            Sel d k j  ->
                match (args, values low AsGiven c m env senv args)
                    ([a], [Ok (Constructed l fs)]) ->
                        match (sort_here c senv a, sort_here c senv t)
                            (Ok (Data _ sargs), Ok fs_sort) ->
                                let got = m.wrong_sel d k j sargs (Constructed l fs)
                                have given_at c m n fs_sort h got
                            _                               -> auto
                    _                              -> auto
            Fun f      -> have call_fuel low low2 c m n senv t f (values low AsGiven c m env senv args)

lemma call_fuel low low2 c m n senv t f rs : low~Lower, low2~Lower, c~Context, m~Model, n~Nat, senv~List Sort, t~Term,
                                             f~Nat, rs~List (Result Value Unknown)
    ensures call low AsGiven c m senv t f rs == call low2 AsGiven c (with_fuel m n) senv t f rs
    proof
        match (all_known rs, sort_here c senv t)
            (Ok vs, Ok s) ->
                have given_at c m n s (Fun f) (m.funs f vs)
            _             -> auto

lemma prim_fuel low low2 c m n env senv t op args : low~Lower, low2~Lower, c~Context, m~Model, n~Nat,
                                                    env~List (Result Value Unknown), senv~List Sort, t~Term, op~Op,
                                                    args~List Term
    ensures prim low AsGiven c m env senv t op args == prim low2 AsGiven c (with_fuel m n) env senv t op args
    proof
        have given_fuel c m n
        have values_fuel low low2 c m n env senv args
        have conj_fuel low low2 c m n env senv args
        have disj_fuel low low2 c m n env senv args
        match args
            [a]       -> have value_fuel low low2 c m n env senv a
            [a, b]    ->
                have value_fuel low low2 c m n env senv a
                have value_fuel low low2 c m n env senv b
                let x = value low AsGiven c m env senv a
                let y = value low AsGiven c m env senv b
                match op
                    Select ->
                        match (x, y, sort_here c senv a, sort_here c senv t)
                            (Ok (ArrayElem k), Ok j, Ok sa, Ok w) ->
                                have given_at c m n w (Prim Select) (m.select sa k j)
                            _                                     -> auto
                    SeqNth ->
                        match (items x, as_int y, sort_here c senv t)
                            (Ok xs, Ok i, Ok e) ->
                                have given_at c m n e (Prim SeqNth) (m.nth_out e xs i)
                            _                   -> auto
                    _      -> auto
            [a, b, d] ->
                have value_fuel low low2 c m n env senv a
                have value_fuel low low2 c m n env senv b
                have value_fuel low low2 c m n env senv d
            _         -> auto

lemma values_fuel low low2 c m n env senv ts : low~Lower, low2~Lower, c~Context, m~Model, n~Nat,
                                               env~List (Result Value Unknown), senv~List Sort, ts~List Term
    ensures values low AsGiven c m env senv ts == values low2 AsGiven c (with_fuel m n) env senv ts
    proof
        match ts
            []        -> auto
            t :: rest ->
                have value_fuel low low2 c m n env senv t
                have values_fuel low low2 c m n env senv rest

lemma bound_fuel low low2 c m n env senv bs : low~Lower, low2~Lower, c~Context, m~Model, n~Nat,
                                              env~List (Result Value Unknown), senv~List Sort, bs~List (Name, Term)
    ensures bound low AsGiven c m env senv bs == bound low2 AsGiven c (with_fuel m n) env senv bs
    proof
        match bs
            []             -> auto
            (_, t) :: rest ->
                have value_fuel low low2 c m n env senv t
                have bound_fuel low low2 c m n env senv rest

lemma conj_fuel low low2 c m n env senv ts : low~Lower, low2~Lower, c~Context, m~Model, n~Nat,
                                             env~List (Result Value Unknown), senv~List Sort, ts~List Term
    ensures conj low AsGiven c m env senv ts == conj low2 AsGiven c (with_fuel m n) env senv ts
    proof
        match ts
            []        -> auto
            t :: rest ->
                have value_fuel low low2 c m n env senv t
                have conj_fuel low low2 c m n env senv rest

lemma disj_fuel low low2 c m n env senv ts : low~Lower, low2~Lower, c~Context, m~Model, n~Nat,
                                             env~List (Result Value Unknown), senv~List Sort, ts~List Term
    ensures disj low AsGiven c m env senv ts == disj low2 AsGiven c (with_fuel m n) env senv ts
    proof
        match ts
            []        -> auto
            t :: rest ->
                have value_fuel low low2 c m n env senv t
                have disj_fuel low low2 c m n env senv rest

# The meaning of a term is the same whatever the fuel.
export lemma eval_fuel c m n t : c~Context, m~Model, n~Nat, t~Term
    ensures eval c m t == eval c (with_fuel m n) t
    proof
        have value_fuel (level AsGiven c m m.fuel) (level AsGiven c (with_fuel m n) n) c m n [] [] t

# So is whether an axiom holds at values.
export lemma holds_at_fuel c m n a vs : c~Context, m~Model, n~Nat, a~Axiom, vs~List Value
    ensures holds_at c m a vs == holds_at c (with_fuel m n) a vs
    proof
        have fields_of_sort_fuel c m n (term.var_sorts a.vars) vs
        have values_of_sorts c m (term.var_sorts a.vars) vs == values_of_sorts c (with_fuel m n) (term.var_sorts a.vars) vs
        let env = list.reverse (list.map (\v -> Ok v) vs)
        have value_fuel (level AsGiven c m m.fuel) (level AsGiven c (with_fuel m n) n) c m n env (term.binder_env a.vars) a.body

# So are `holds`, `fails` and `holds_all`.
export lemma holds_fuel c m n t : c~Context, m~Model, n~Nat, t~Term
    ensures holds c m t == holds c (with_fuel m n) t
    proof
        have eval_fuel c m n t

export lemma fails_fuel c m n t : c~Context, m~Model, n~Nat, t~Term
    ensures fails c m t == fails c (with_fuel m n) t
    proof
        have eval_fuel c m n t

export lemma holds_all_fuel c m n ts : c~Context, m~Model, n~Nat, ts~List Term
    ensures holds_all c m ts == holds_all c (with_fuel m n) ts
    proof
        match ts
            []        -> auto
            t :: rest ->
                have holds_fuel c m n t
                have holds_all_fuel c m n rest

# So is whether a term has a value of its sort.
export lemma has_value_fuel c m n t : c~Context, m~Model, n~Nat, t~Term
    ensures has_value c m t == has_value c (with_fuel m n) t
    proof
        have eval_fuel c m n t
        match (term.sort_of (term.signature c) [] t, eval c m t)
            (Ok s, Ok v) -> have of_sort_fuel c m n s v
            _            -> auto

# So is whether the model answers a read.
export lemma gives_fuel c m n r : c~Context, m~Model, n~Nat, r~Read
    ensures gives c m r == gives c (with_fuel m n) r
    proof
        match r
            FunAt f vs              -> have gives_fun_fuel c m n f vs
            NthOutAt e xs i         -> have gives_nth_out_fuel c m n e xs i
            WrongSelAt d k j args v -> have gives_wrong_sel_fuel c m n d k j args v
            _                       -> auto

lemma answers_with_fuel c m n s got : c~Context, m~Model, n~Nat, s~Sort, got~Option Value
    ensures answers_with c m s got == answers_with c (with_fuel m n) s got
    proof
        match got
            Some v -> have of_sort_fuel c m n s v
            None   -> auto

lemma gives_fun_fuel c m n f vs : c~Context, m~Model, n~Nat, f~Nat, vs~List Value
    ensures gives_fun c m f vs == gives_fun c (with_fuel m n) f vs
    proof
        let sig = term.signature c
        if f < len sig.funs
            have fields_of_sort_fuel c m n sig.funs[f].params vs
            have answers_with_fuel c m n sig.funs[f].result (m.funs f vs)
        else
            auto

lemma gives_nth_out_fuel c m n e xs i : c~Context, m~Model, n~Nat, e~Sort, xs~List Value, i~Int
    ensures gives_nth_out c m e xs i == gives_nth_out c (with_fuel m n) e xs i
    proof
        have all_of_sort_fuel c m n e xs
        have answers_with_fuel c m n e (m.nth_out e xs i)

lemma gives_wrong_sel_fuel c m n d k j args v : c~Context, m~Model, n~Nat, d~Nat, k~Nat, j~Nat, args~List Sort, v~Value
    ensures gives_wrong_sel c m d k j args v == gives_wrong_sel c (with_fuel m n) d k j args v
    proof
        have of_sort_fuel c m n (Data d args) v
        match term.ctor (term.signature c) d k
            Some kc ->
                match list.head (list.drop j kc.fields)
                    Some fd -> have answers_with_fuel c m n (term.instantiate args fd.sort) (m.wrong_sel d k j args v)
                    None    -> auto
            None    -> auto

# So are the array laws, and whether the model answers the arrays' reads.
lemma sorted_at_fuel c m n s k i x : c~Context, m~Model, n~Nat, s~Sort, k~Nat, i~Value, x~Value
    ensures sorted_at c m s k i x == sorted_at c (with_fuel m n) s k i x
        and index_and_value c m s i x == index_and_value c (with_fuel m n) s i x
    proof
        match s
            Arr ix w ->
                have of_sort_fuel c m n ix i
                have of_sort_fuel c m n w x
            _        -> auto

lemma lambda_sorted_fuel c m n s env senv xs body : c~Context, m~Model, n~Nat, s~Sort, env~List Value, senv~List Sort,
                                                    xs~Sort, body~Term
    ensures lambda_sorted c m s env senv xs body == lambda_sorted c (with_fuel m n) s env senv xs body
    proof
        have fields_of_sort_fuel c m n (list.reverse senv) (list.reverse env)

lemma const_law_fuel c m n s x i : c~Context, m~Model, n~Nat, s~Sort, x~Value, i~Value
    ensures const_law c m s x i == const_law c (with_fuel m n) s x i
    proof
        have sorted_at_fuel c m n s 0 i x

lemma store_law_fuel c m n s k j x i : c~Context, m~Model, n~Nat, s~Sort, k~Nat, j~Value, x~Value, i~Value
    ensures store_law c m s k j x i == store_law c (with_fuel m n) s k j x i
    proof
        have sorted_at_fuel c m n s k j x
        have sorted_at_fuel c m n s k i x

lemma sum_law_fuel c m n s a b i : c~Context, m~Model, n~Nat, s~Sort, a~Nat, b~Nat, i~Value
    ensures sum_law c m s a b i == sum_law c (with_fuel m n) s a b i
    proof
        have sorted_at_fuel c m n s a i (Integer 0)

lemma ext_law_fuel c m n s a b : c~Context, m~Model, n~Nat, s~Sort, a~Nat, b~Nat
    ensures ext_law c m s a b == ext_law c (with_fuel m n) s a b
    proof
        match s
            Arr ix _ -> have of_sort_fuel c m n ix (m.differ s a b)
            _        -> auto

lemma lambda_law_fuel c m n s env senv xs body i : c~Context, m~Model, n~Nat, s~Sort, env~List Value, senv~List Sort,
                                                   xs~Sort, body~Term, i~Value
    ensures lambda_law c m s env senv xs body i == lambda_law c (with_fuel m n) s env senv xs body i
    proof
        have lambda_sorted_fuel c m n s env senv xs body
        have of_sort_fuel c m n xs i
        let at = Ok i :: list.map (\v -> Ok v) env
        have value_fuel (level AsGiven c m m.fuel) (level AsGiven c (with_fuel m n) n) c m n at (xs :: senv) body

export lemma arrays_ok_at_fuel c m n s a b i j x env senv xs body : c~Context, m~Model, n~Nat, s~Sort, a~Nat, b~Nat,
                                                                    i~Value, j~Value, x~Value, env~List Value,
                                                                    senv~List Sort, xs~Sort, body~Term
    ensures arrays_ok_at c m s a b i j x env senv xs body == arrays_ok_at c (with_fuel m n) s a b i j x env senv xs body
    proof
        have const_law_fuel c m n s x i
        have store_law_fuel c m n s a j x i
        have sum_law_fuel c m n s a b i
        have lambda_law_fuel c m n s env senv xs body i
        have ext_law_fuel c m n s a b

lemma gives_select_fuel c m n s k i : c~Context, m~Model, n~Nat, s~Sort, k~Nat, i~Value
    ensures gives_select c m s k i == gives_select c (with_fuel m n) s k i
    proof
        match s
            Arr ix w ->
                have of_sort_fuel c m n ix i
                match m.select s k i
                    Some v -> have of_sort_fuel c m n w v
                    None   -> auto
            _        -> auto

lemma gives_const_fuel c m n s x : c~Context, m~Model, n~Nat, s~Sort, x~Value
    ensures gives_const c m s x == gives_const c (with_fuel m n) s x
    proof
        match s
            Arr _ w -> have of_sort_fuel c m n w x
            _       -> auto

export lemma arrays_total_at_fuel c m n s a b i j x env senv xs body : c~Context, m~Model, n~Nat, s~Sort, a~Nat, b~Nat,
                                                                       i~Value, j~Value, x~Value, env~List Value,
                                                                       senv~List Sort, xs~Sort, body~Term
    ensures arrays_total_at c m s a b i j x env senv xs body
        == arrays_total_at c (with_fuel m n) s a b i j x env senv xs body
    proof
        have gives_select_fuel c m n s a i
        have gives_const_fuel c m n s x
        have sorted_at_fuel c m n s a j x
        have lambda_sorted_fuel c m n s env senv xs body

# ── Monotonicity ─────────────────────────────────────────────────────────────
# A definite answer in a model is the answer in every model that agrees
# with it wherever it answers (#86): `monotone`. A definite answer of
# unfolding is the answer at more fuel: `unfolding_more_fuel`.

# What a model is asked by `eval`: each of `Model`'s `funs`, `select`,
# `const`, `store`, `sum`, `lambda`, `div_zero`, `mod_zero`, `nth_out` and
# `wrong_sel` at its arguments. Not `array_in` and `domain`, which answer
# with a `Bool` and a `Domain` and get premises of their own in
# `monotone`, nor `differ` and `fuel`, which `eval` (the meaning) doesn't
# consult.
export enum Asked
    FunsAt f vs                : f~Nat, vs~List Value
    SelectAt s k i             : s~Sort, k~Nat, i~Value
    ConstAt s v                : s~Sort, v~Value
    StoreAt s k i v            : s~Sort, k~Nat, i~Value, v~Value
    SumAt s a b                : s~Sort, a~Nat, b~Nat
    LambdaAt s env senv x body : s~Sort, env~List Value, senv~List Sort, x~Sort, body~Term
    DivAt n                    : n~Int
    ModAt n                    : n~Int
    NthAt s xs i               : s~Sort, xs~List Value, i~Int
    SelAt d k j args v         : d~Nat, k~Nat, j~Nat, args~List Sort, v~Value

# What `m` says to `q`, as a value (an array's number as `ArrayElem`, an
# integer as `Integer`); `None` where it doesn't say.
export transparent fn said m q -> r : m~Model, q~Asked, r~Option Value
    match q
        FunsAt f vs                -> m.funs f vs
        SelectAt s k i             -> m.select s k i
        ConstAt s v                -> number_said (m.const s v)
        StoreAt s k i v            -> number_said (m.store s k i v)
        SumAt s a b                -> number_said (m.sum s a b)
        LambdaAt s env senv x body -> number_said (m.lambda s env senv x body)
        DivAt n                    -> integer_said (m.div_zero n)
        ModAt n                    -> integer_said (m.mod_zero n)
        NthAt s xs i               -> m.nth_out s xs i
        SelAt d k j args v         -> m.wrong_sel d k j args v

export transparent fn number_said r -> v : r~Option Nat, v~Option Value
    match r
        Some k -> Some (ArrayElem k)
        None   -> None

export transparent fn integer_said r -> v : r~Option Int, v~Option Value
    match r
        Some n -> Some (Integer n)
        None   -> None

# Whether `r2` is `r1` wherever `r1` is a value.
fn refines r1 r2 -> b : r1~Result Value Unknown, r2~Result Value Unknown, b~Bool
    match r1
        Ok v  -> r2 == Ok v
        Err _ -> True

# Whether each of `e2` refines the one in the same place of `e1`.
fn envs_refine e1 e2 -> b : e1~List (Result Value Unknown), e2~List (Result Value Unknown), b~Bool
    match (e1, e2)
        ([], [])           -> True
        (x :: xr, y :: yr) -> refines x y and envs_refine xr yr
        _                  -> False

lemma of_sort_mono c m n s v : c~Context, m~Model, n~Model, s~Sort, v~Value, of_sort c m s v,
                               arrays: (forall t k : t~Sort, k~Nat, m.array_in t k, n.array_in t k),
                               domains: (forall u args k : u~Nat, args~List Sort, k~Nat,
                                         of_sort c m (Unin u args) (Element k), of_sort c n (Unin u args) (Element k))
    ensures of_sort c n s v
    proof
        match (s, v)
            (Seq e, Sequence xs)            -> have all_of_sort_mono c m n e xs
            (Arr _ _, ArrayElem k)          -> have arrays s k
            (Data d args, Constructed k fs) ->
                match term.ctor (term.signature c) d k
                    Some kc -> have fields_of_sort_mono c m n (list.map (term.instantiate args) (term.field_sorts kc.fields)) fs
                    None    -> auto
            (Unin u args, Element k)        -> have domains u args k
            _                               -> auto

lemma all_of_sort_mono c m n s vs : c~Context, m~Model, n~Model, s~Sort, vs~List Value, all_of_sort c m s vs,
                                    arrays: (forall t k : t~Sort, k~Nat, m.array_in t k, n.array_in t k),
                                    domains: (forall u args k : u~Nat, args~List Sort, k~Nat,
                                              of_sort c m (Unin u args) (Element k), of_sort c n (Unin u args) (Element k))
    ensures all_of_sort c n s vs
    proof
        match vs
            []        -> auto
            v :: rest ->
                have of_sort_mono c m n s v
                have all_of_sort_mono c m n s rest

lemma fields_of_sort_mono c m n ss vs : c~Context, m~Model, n~Model, ss~List Sort, vs~List Value, fields_of_sort c m ss vs,
                                        arrays: (forall t k : t~Sort, k~Nat, m.array_in t k, n.array_in t k),
                                        domains: (forall u args k : u~Nat, args~List Sort, k~Nat,
                                                  of_sort c m (Unin u args) (Element k), of_sort c n (Unin u args) (Element k))
    ensures fields_of_sort c n ss vs
    proof
        match (ss, vs)
            (s :: sr, v :: vr) ->
                have of_sort_mono c m n s v
                have fields_of_sort_mono c m n sr vr
            _                  -> auto

fn at e i -> r : e~List (Result Value Unknown), i~Nat, r~Result Value Unknown
    match list.head (list.drop i e)
        Some v -> v
        None   -> Err IllSorted

fn lists_refine p q -> b : p~Result (List Value) Unknown, q~Result (List Value) Unknown, b~Bool
    match p
        Ok x  -> q == Ok x
        Err _ -> True

fn opts_refine p q -> b : p~Option Value, q~Option Value, b~Bool
    match p
        Some x -> q == Some x
        None   -> True

fn bools_refine p q -> b : p~Result Bool Unknown, q~Result Bool Unknown, b~Bool
    match p
        Ok x  -> q == Ok x
        Err _ -> True

lemma said_refines c m n q : c~Context, m~Model, n~Model, q~Asked,
                             said: (forall q2 x : q2~Asked, x~Value, said m q2 == Some x, said n q2 == Some x)
    ensures opts_refine (said m q) (said n q)
    proof
        match said m q
            Some x -> have said q x
            None   -> auto

lemma at_mono e1 e2 i : e1~List (Result Value Unknown), e2~List (Result Value Unknown), i~Nat, envs_refine e1 e2
    ensures refines (at e1 i) (at e2 i)
    proof
        match (e1, e2)
            (_ :: xr, _ :: yr) -> if i == 0 then auto else have at_mono xr yr (i - 1)
            _                  -> auto

lemma known_mono e1 e2 : e1~List (Result Value Unknown), e2~List (Result Value Unknown), envs_refine e1 e2
    ensures lists_refine (all_known e1) (all_known e2)
    proof
        match (e1, e2)
            (_ :: xr, _ :: yr) -> have known_mono xr yr
            _                  -> auto

lemma reverse_mono a b e1 e2 : a~List (Result Value Unknown), b~List (Result Value Unknown), e1~List (Result Value Unknown),
                               e2~List (Result Value Unknown), envs_refine a b, envs_refine e1 e2
    ensures envs_refine (list.reverse a ++ e1) (list.reverse b ++ e2)
    proof
        match (a, b)
            (x :: ar, y :: br) ->
                have list.reverse_cons_append ar x e1
                have list.reverse_cons_append br y e2
                have reverse_mono ar br (x :: e1) (y :: e2)
            _                  -> auto

lemma given_mono c m n s h x y : c~Context, m~Model, n~Model, s~Sort, h~Head, x~Option Value, y~Option Value,
                                 opts_refine x y,
                                 arrays: (forall t k : t~Sort, k~Nat, m.array_in t k, n.array_in t k),
                                 domains: (forall u args k : u~Nat, args~List Sort, k~Nat,
                                           of_sort c m (Unin u args) (Element k), of_sort c n (Unin u args) (Element k))
    ensures refines (given c m s h x) (given c n s h y)
    proof
        match x
            Some v -> if of_sort c m s v then have of_sort_mono c m n s v else auto
            None   -> auto

lemma value_mono lm ln mode c m n e1 e2 senv t : lm~Lower, ln~Lower, mode~Mode, c~Context, m~Model, n~Model, e1~List (Result Value Unknown),
                                                 e2~List (Result Value Unknown), senv~List Sort, t~Term, envs_refine e1 e2,
                                                 lows: (forall f1 f2 s2 u : f1~List (Result Value Unknown), f2~List (Result Value Unknown), s2~List Sort, u~Term, envs_refine f1 f2,
                                                        mode == Unfolding implies refines (lm.value f1 s2 u) (ln.value f2 s2 u)),
                                                 said: (forall q x : q~Asked, x~Value, said m q == Some x, said n q == Some x),
                                                 arrays: (forall t k : t~Sort, k~Nat, m.array_in t k, n.array_in t k),
                                                 domains: (forall u args k : u~Nat, args~List Sort, k~Nat, of_sort c m (Unin u args) (Element k),
                                                           of_sort c n (Unin u args) (Element k))
    ensures refines (value lm mode c m e1 senv t) (value ln mode c n e2 senv t)
    proof
        match t
            Var i          -> have at_mono e1 e2 i
            App h args     -> have apply_mono lm ln mode c m n e1 e2 senv t h args
            Let binds body ->
                have bound_mono lm ln mode c m n e1 e2 senv binds
                have reverse_mono (bound lm mode c m e1 senv binds) (bound ln mode c n e2 senv binds) e1 e2
                match term.sorts_of (term.signature c) senv (term.bind_terms binds)
                    Ok ss ->
                        let f1 = list.reverse (bound lm mode c m e1 senv binds) ++ e1
                        let f2 = list.reverse (bound ln mode c n e2 senv binds) ++ e2
                        have value_mono lm ln mode c m n f1 f2 (list.reverse ss ++ senv) body
                    Err _ -> auto
            Lam _ x body   ->
                have known_mono e1 e2
                match (sort_here c senv t, all_known e1)
                    (Ok s, Ok vs) ->
                        match m.lambda s vs senv x body
                            Some k ->
                                have said_refines c m n (LambdaAt s vs senv x body)
                                if m.array_in s k then have arrays s k else auto
                            None   -> auto
                    _             -> auto

lemma values_mono lm ln mode c m n e1 e2 senv ts : lm~Lower, ln~Lower, mode~Mode, c~Context, m~Model, n~Model, e1~List (Result Value Unknown),
                                                   e2~List (Result Value Unknown), senv~List Sort, ts~List Term, envs_refine e1 e2,
                                                   lows: (forall f1 f2 s2 u : f1~List (Result Value Unknown), f2~List (Result Value Unknown), s2~List Sort, u~Term, envs_refine f1 f2,
                                                          mode == Unfolding implies refines (lm.value f1 s2 u) (ln.value f2 s2 u)),
                                                   said: (forall q x : q~Asked, x~Value, said m q == Some x, said n q == Some x),
                                                   arrays: (forall t k : t~Sort, k~Nat, m.array_in t k, n.array_in t k),
                                                   domains: (forall u args k : u~Nat, args~List Sort, k~Nat, of_sort c m (Unin u args) (Element k),
                                                             of_sort c n (Unin u args) (Element k))
    ensures envs_refine (values lm mode c m e1 senv ts) (values ln mode c n e2 senv ts)
    proof
        match ts
            []        -> auto
            t :: rest ->
                have value_mono lm ln mode c m n e1 e2 senv t
                have values_mono lm ln mode c m n e1 e2 senv rest

lemma bound_mono lm ln mode c m n e1 e2 senv bs : lm~Lower, ln~Lower, mode~Mode, c~Context, m~Model, n~Model, e1~List (Result Value Unknown),
                                                  e2~List (Result Value Unknown), senv~List Sort, bs~List (term.Name, Term), envs_refine e1 e2,
                                                  lows: (forall f1 f2 s2 u : f1~List (Result Value Unknown), f2~List (Result Value Unknown), s2~List Sort, u~Term, envs_refine f1 f2,
                                                         mode == Unfolding implies refines (lm.value f1 s2 u) (ln.value f2 s2 u)),
                                                  said: (forall q x : q~Asked, x~Value, said m q == Some x, said n q == Some x),
                                                  arrays: (forall t k : t~Sort, k~Nat, m.array_in t k, n.array_in t k),
                                                  domains: (forall u args k : u~Nat, args~List Sort, k~Nat, of_sort c m (Unin u args) (Element k),
                                                            of_sort c n (Unin u args) (Element k))
    ensures envs_refine (bound lm mode c m e1 senv bs) (bound ln mode c n e2 senv bs)
    proof
        match bs
            []             -> auto
            (_, t) :: rest ->
                have value_mono lm ln mode c m n e1 e2 senv t
                have bound_mono lm ln mode c m n e1 e2 senv rest

lemma conj_mono lm ln mode c m n e1 e2 senv ts : lm~Lower, ln~Lower, mode~Mode, c~Context, m~Model, n~Model, e1~List (Result Value Unknown),
                                                 e2~List (Result Value Unknown), senv~List Sort, ts~List Term, envs_refine e1 e2,
                                                 lows: (forall f1 f2 s2 u : f1~List (Result Value Unknown), f2~List (Result Value Unknown), s2~List Sort, u~Term, envs_refine f1 f2,
                                                        mode == Unfolding implies refines (lm.value f1 s2 u) (ln.value f2 s2 u)),
                                                 said: (forall q x : q~Asked, x~Value, said m q == Some x, said n q == Some x),
                                                 arrays: (forall t k : t~Sort, k~Nat, m.array_in t k, n.array_in t k),
                                                 domains: (forall u args k : u~Nat, args~List Sort, k~Nat, of_sort c m (Unin u args) (Element k),
                                                           of_sort c n (Unin u args) (Element k))
    ensures bools_refine (conj lm mode c m e1 senv ts) (conj ln mode c n e2 senv ts)
    proof
        match ts
            []        -> auto
            t :: rest ->
                have value_mono lm ln mode c m n e1 e2 senv t
                have conj_mono lm ln mode c m n e1 e2 senv rest

lemma disj_mono lm ln mode c m n e1 e2 senv ts : lm~Lower, ln~Lower, mode~Mode, c~Context, m~Model, n~Model, e1~List (Result Value Unknown),
                                                 e2~List (Result Value Unknown), senv~List Sort, ts~List Term, envs_refine e1 e2,
                                                 lows: (forall f1 f2 s2 u : f1~List (Result Value Unknown), f2~List (Result Value Unknown), s2~List Sort, u~Term, envs_refine f1 f2,
                                                        mode == Unfolding implies refines (lm.value f1 s2 u) (ln.value f2 s2 u)),
                                                 said: (forall q x : q~Asked, x~Value, said m q == Some x, said n q == Some x),
                                                 arrays: (forall t k : t~Sort, k~Nat, m.array_in t k, n.array_in t k),
                                                 domains: (forall u args k : u~Nat, args~List Sort, k~Nat, of_sort c m (Unin u args) (Element k),
                                                           of_sort c n (Unin u args) (Element k))
    ensures bools_refine (disj lm mode c m e1 senv ts) (disj ln mode c n e2 senv ts)
    proof
        match ts
            []        -> auto
            t :: rest ->
                have value_mono lm ln mode c m n e1 e2 senv t
                have disj_mono lm ln mode c m n e1 e2 senv rest

lemma apply_mono lm ln mode c m n e1 e2 senv t h args : lm~Lower, ln~Lower, mode~Mode, c~Context, m~Model, n~Model, e1~List (Result Value Unknown),
                                                        e2~List (Result Value Unknown), senv~List Sort, t~Term, h~Head, args~List Term, envs_refine e1 e2,
                                                        lows: (forall f1 f2 s2 u : f1~List (Result Value Unknown), f2~List (Result Value Unknown), s2~List Sort, u~Term, envs_refine f1 f2,
                                                               mode == Unfolding implies refines (lm.value f1 s2 u) (ln.value f2 s2 u)),
                                                        said: (forall q x : q~Asked, x~Value, said m q == Some x, said n q == Some x),
                                                        arrays: (forall t k : t~Sort, k~Nat, m.array_in t k, n.array_in t k),
                                                        domains: (forall u args k : u~Nat, args~List Sort, k~Nat, of_sort c m (Unin u args) (Element k),
                                                                  of_sort c n (Unin u args) (Element k))
    ensures refines (apply lm mode c m e1 senv t h args) (apply ln mode c n e2 senv t h args)
    proof
        have values_mono lm ln mode c m n e1 e2 senv args
        match h
            Prim op    -> have prim_mono lm ln mode c m n e1 e2 senv t op args
            ConstArr s ->
                match values lm mode c m e1 senv args
                    [Ok x] ->
                        match m.const s x
                            Some k ->
                                have said_refines c m n (ConstAt s x)
                                if m.array_in s k then have arrays s k else auto
                            None   -> auto
                    _      -> auto
            Con _ _ _  -> have known_mono (values lm mode c m e1 senv args) (values ln mode c n e2 senv args)
            Sel d k j  ->
                match (args, values lm mode c m e1 senv args)
                    ([a], [Ok (Constructed l fs)]) ->
                        if k == l
                            auto
                        else
                            match (sort_here c senv a, sort_here c senv t)
                                (Ok (Data _ sargs), Ok fs_sort) ->
                                    let got = m.wrong_sel d k j sargs (Constructed l fs)
                                    have said_refines c m n (SelAt d k j sargs (Constructed l fs))
                                    have given_mono c m n fs_sort h got (n.wrong_sel d k j sargs (Constructed l fs))
                                _                               -> auto
                    _                              -> auto
            Fun f      ->
                let r1 = values lm mode c m e1 senv args
                let r2 = values ln mode c n e2 senv args
                have known_mono r1 r2
                match (mode, definition (term.defs c) f, all_known r1, sort_here c senv t)
                    (Unfolding, Some d, _, _) ->
                        if unfolds d
                            have reverse_mono r1 r2 [] []
                            have list.append_nil (list.reverse r1)
                            have list.append_nil (list.reverse r2)
                            have lows (list.reverse r1) (list.reverse r2) (term.binder_env d.params) d.body
                        else
                            auto
                    (_, _, Ok vs, Ok s)       ->
                        have said_refines c m n (FunsAt f vs)
                        have given_mono c m n s (Fun f) (m.funs f vs) (n.funs f vs)
                    _                         -> auto
            _          -> auto

lemma concat_mono r1 r2 : r1~List (Result Value Unknown), r2~List (Result Value Unknown), envs_refine r1 r2
    ensures lists_refine (concat_all r1) (concat_all r2)
    proof
        match (r1, r2)
            (_ :: xr, _ :: yr) -> have concat_mono xr yr
            _                  -> auto

lemma prim_mono lm ln mode c m n e1 e2 senv t op args : lm~Lower, ln~Lower, mode~Mode, c~Context, m~Model, n~Model, e1~List (Result Value Unknown),
                                                        e2~List (Result Value Unknown), senv~List Sort, t~Term, op~Op, args~List Term, envs_refine e1 e2,
                                                        lows: (forall f1 f2 s2 u : f1~List (Result Value Unknown), f2~List (Result Value Unknown), s2~List Sort, u~Term, envs_refine f1 f2,
                                                               mode == Unfolding implies refines (lm.value f1 s2 u) (ln.value f2 s2 u)),
                                                        said: (forall q x : q~Asked, x~Value, said m q == Some x, said n q == Some x),
                                                        arrays: (forall t k : t~Sort, k~Nat, m.array_in t k, n.array_in t k),
                                                        domains: (forall u args k : u~Nat, args~List Sort, k~Nat, of_sort c m (Unin u args) (Element k),
                                                                  of_sort c n (Unin u args) (Element k))
    ensures refines (prim lm mode c m e1 senv t op args) (prim ln mode c n e2 senv t op args)
    proof
        match (op, args)
            (And, _)           -> have conj_mono lm ln mode c m n e1 e2 senv args
            (Or, _)            -> have disj_mono lm ln mode c m n e1 e2 senv args
            (SeqConcat, _)     ->
                have values_mono lm ln mode c m n e1 e2 senv args
                have concat_mono (values lm mode c m e1 senv args) (values ln mode c n e2 senv args)
            (Div, [a, b])      ->
                have value_mono lm ln mode c m n e1 e2 senv a
                have value_mono lm ln mode c m n e1 e2 senv b
                match (value lm mode c m e1 senv a, value lm mode c m e1 senv b)
                    (Ok (Integer x), Ok (Integer 0)) -> have said_refines c m n (DivAt x)
                    _                                -> auto
            (Mod, [a, b])      ->
                have value_mono lm ln mode c m n e1 e2 senv a
                have value_mono lm ln mode c m n e1 e2 senv b
                match (value lm mode c m e1 senv a, value lm mode c m e1 senv b)
                    (Ok (Integer x), Ok (Integer 0)) -> have said_refines c m n (ModAt x)
                    _                                -> auto
            (Select, [a, i])   ->
                have value_mono lm ln mode c m n e1 e2 senv a
                have value_mono lm ln mode c m n e1 e2 senv i
                match (value lm mode c m e1 senv a, value lm mode c m e1 senv i, sort_here c senv a, sort_here c senv t)
                    (Ok (ArrayElem k), Ok j, Ok s, Ok w) ->
                        have said_refines c m n (SelectAt s k j)
                        have given_mono c m n w (Prim Select) (m.select s k j) (n.select s k j)
                    _                                    -> auto
            (Store, [a, i, v]) ->
                have value_mono lm ln mode c m n e1 e2 senv a
                have value_mono lm ln mode c m n e1 e2 senv i
                have value_mono lm ln mode c m n e1 e2 senv v
                match (value lm mode c m e1 senv a, value lm mode c m e1 senv i, value lm mode c m e1 senv v, sort_here c senv t)
                    (Ok (ArrayElem k), Ok j, Ok y, Ok s) ->
                        match m.store s k j y
                            Some l ->
                                have said_refines c m n (StoreAt s k j y)
                                if m.array_in s l then have arrays s l else auto
                            None   -> auto
                    _                                    -> auto
            (MapAdd, [a, b])   ->
                have value_mono lm ln mode c m n e1 e2 senv a
                have value_mono lm ln mode c m n e1 e2 senv b
                match (value lm mode c m e1 senv a, value lm mode c m e1 senv b, sort_here c senv t)
                    (Ok (ArrayElem p), Ok (ArrayElem q), Ok s) ->
                        match m.sum s p q
                            Some l ->
                                have said_refines c m n (SumAt s p q)
                                if m.array_in s l then have arrays s l else auto
                            None   -> auto
                    _                                          -> auto
            (SeqNth, [a, i])   ->
                have value_mono lm ln mode c m n e1 e2 senv a
                have value_mono lm ln mode c m n e1 e2 senv i
                match (value lm mode c m e1 senv a, value lm mode c m e1 senv i, sort_here c senv t)
                    (Ok (Sequence xs), Ok (Integer k), Ok s) ->
                        have said_refines c m n (NthAt s xs k)
                        have given_mono c m n s (Prim SeqNth) (m.nth_out s xs k) (n.nth_out s xs k)
                    _                                        -> auto
            (_, [a])           -> have value_mono lm ln mode c m n e1 e2 senv a
            (_, [a, b])        ->
                have value_mono lm ln mode c m n e1 e2 senv a
                have value_mono lm ln mode c m n e1 e2 senv b
            (_, [a, b, d])     ->
                have value_mono lm ln mode c m n e1 e2 senv a
                have value_mono lm ln mode c m n e1 e2 senv b
                have value_mono lm ln mode c m n e1 e2 senv d
            _                  -> auto

lemma refines_ok r1 r2 v : r1~Result Value Unknown, r2~Result Value Unknown, v~Value, refines r1 r2, r1 == Ok v
    ensures r2 == Ok v

lemma eval_is c m t : c~Context, m~Model, t~Term
    ensures eval c m t == (if closed c t then value (level AsGiven c m m.fuel) AsGiven c m [] [] t else Err IllSorted)

# Monotonicity: a definite answer of `eval` in `m` is the answer in every
# model `n` that says what `m` says wherever `m` says something (`said`),
# names as arrays at least the arrays `m` names, and has at least `m`'s
# elements of each uninterpreted sort.
export lemma monotone c m n t v : c~Context, m~Model, n~Model, t~Term, v~Value, eval c m t == Ok v,
                                  said: (forall q x : q~Asked, x~Value, said m q == Some x, said n q == Some x),
                                  arrays: (forall s k : s~Sort, k~Nat, m.array_in s k, n.array_in s k),
                                  domains: (forall u args k : u~Nat, args~List Sort, k~Nat, of_sort c m (Unin u args) (Element k),
                                            of_sort c n (Unin u args) (Element k))
    ensures eval c n t == Ok v
    proof
        have eval_is c m t
        have eval_is c n t
        let r1 = value (level AsGiven c m m.fuel) AsGiven c m [] [] t
        let r2 = value (level AsGiven c n n.fuel) AsGiven c n [] [] t
        have value_mono (level AsGiven c m m.fuel) (level AsGiven c n n.fuel) AsGiven c m n [] [] [] t
        have refines_ok r1 r2 v

# Unfolding at `l` levels answers wherever unfolding at `k <= l` does, and
# the same, whatever the models' fuel (`p`, `q`).
lemma levels_more c m p q k l : c~Context, m~Model, p~Nat, q~Nat, k~Nat, l~Nat, k <= l
    ensures forall e1 e2 senv t : e1~List (Result Value Unknown), e2~List (Result Value Unknown), senv~List Sort, t~Term, envs_refine e1 e2
                                  implies refines ((level Unfolding c (with_fuel m p) k).value e1 senv t) ((level Unfolding c (with_fuel m q) l).value e2 senv t)
    proof
        if k == 0
            auto
        else
            have levels_more c m p q (k - 1) (l - 1)
            have sorts_fuel c m p
            have sorts_fuel c m q
            let lm = level Unfolding c (with_fuel m p) (k - 1)
            let ln = level Unfolding c (with_fuel m q) (l - 1)
            have value_mono lm ln Unfolding c (with_fuel m p) (with_fuel m q) e1 e2 senv t

# Fuel monotonicity: a definite answer of unfolding at some fuel is the
# answer at more fuel.
export lemma unfolding_more_fuel c m t v k l : c~Context, m~Model, t~Term, v~Value, k~Nat, l~Nat, k <= l,
                                               eval_unfolding c (with_fuel m k) t == Ok v
    ensures eval_unfolding c (with_fuel m l) t == Ok v
    proof
        have levels_more c m k l k l
        have sorts_fuel c m k
        have sorts_fuel c m l
        let lm = level Unfolding c (with_fuel m k) k
        let ln = level Unfolding c (with_fuel m l) l
        have value_mono lm ln Unfolding c (with_fuel m k) (with_fuel m l) [] [] [] t
        have refines_ok (value lm Unfolding c (with_fuel m k) [] [] t) (value ln Unfolding c (with_fuel m l) [] [] t) v

# ── In a total model every term has a value ──────────────────────────────────

# Whether each of `rs` is a value of the sort in the same place of `ss`.
fn results_of_sorts c m rs ss -> r : c~Context, m~Model, rs~List (Result Value Unknown), ss~List Sort, r~Bool
    match (rs, ss)
        ([], [])              -> True
        (Ok v :: rr, s :: sr) -> of_sort c m s v and results_of_sorts c m rr sr
        _                     -> False

lemma all_of_sort_append c m s xs ys : c~Context, m~Model, s~Sort, xs~List Value, ys~List Value, all_of_sort c m s xs,
                                       all_of_sort c m s ys
    ensures all_of_sort c m s (xs ++ ys)
    proof
        match xs
            []        -> auto
            _ :: rest -> have all_of_sort_append c m s rest ys

lemma all_of_sort_take c m s n xs : c~Context, m~Model, s~Sort, n~Nat, xs~List Value, all_of_sort c m s xs
    ensures all_of_sort c m s (list.take n xs)
    proof
        match xs
            []        -> auto
            _ :: rest ->
                match n
                    0 -> auto
                    _ -> have all_of_sort_take c m s (n - 1) rest

lemma all_of_sort_drop c m s n xs : c~Context, m~Model, s~Sort, n~Nat, xs~List Value, all_of_sort c m s xs
    ensures all_of_sort c m s (list.drop n xs)
    proof
        match xs
            []        -> auto
            _ :: rest ->
                match n
                    0 -> auto
                    _ -> have all_of_sort_drop c m s (n - 1) rest

lemma all_of_sort_nth c m s xs i : c~Context, m~Model, s~Sort, xs~List Value, i~Nat, all_of_sort c m s xs,
                                   i < list.length xs
    ensures match list.head (list.drop i xs)
        Some x -> of_sort c m s x
        None   -> False
    proof
        match xs
            []        -> auto
            _ :: rest ->
                match i
                    0 -> auto
                    _ -> have all_of_sort_nth c m s rest (i - 1)

lemma results_reverse c m rs ss env senv : c~Context, m~Model, rs~List (Result Value Unknown), ss~List Sort,
                                           env~List (Result Value Unknown), senv~List Sort, results_of_sorts c m rs ss,
                                           results_of_sorts c m env senv
    ensures results_of_sorts c m (list.reverse rs ++ env) (list.reverse ss ++ senv)
    proof
        match (rs, ss)
            ([], [])           ->
                have list.length_reverse rs
                have list.length_reverse ss
            (r :: rr, s :: sr) ->
                have list.reverse_cons_append rr r env
                have list.reverse_cons_append sr s senv
                have results_reverse c m rr sr (r :: env) (s :: senv)
            _                  -> auto

# Whether `r` is a value of sort `s`.
fn result_of_sort c m s r -> b : c~Context, m~Model, s~Sort, r~Result Value Unknown, b~Bool
    match r
        Ok v  -> of_sort c m s v
        Err _ -> False

lemma results_nth c m rs ss i : c~Context, m~Model, rs~List (Result Value Unknown), ss~List Sort, i~Nat,
                                results_of_sorts c m rs ss
    ensures match list.head (list.drop i ss)
        Some s ->
            match list.head (list.drop i rs)
                Some r -> result_of_sort c m s r
                None   -> False
        None   -> True
    proof
        match (rs, ss)
            (_ :: rr, _ :: sr) ->
                match i
                    0 -> auto
                    _ -> have results_nth c m rr sr (i - 1)
            _                  -> auto

lemma all_known_total c m rs ss : c~Context, m~Model, rs~List (Result Value Unknown), ss~List Sort,
                                  results_of_sorts c m rs ss
    ensures match all_known rs
        Ok vs -> fields_of_sort c m ss vs
        Err _ -> False
    proof
        match (rs, ss)
            (_ :: rr, _ :: sr) -> have all_known_total c m rr sr
            _                  -> auto

lemma fields_reverse c m ss vs acc_s acc_v : c~Context, m~Model, ss~List Sort, vs~List Value, acc_s~List Sort,
                                             acc_v~List Value, fields_of_sort c m ss vs, fields_of_sort c m acc_s acc_v
    ensures fields_of_sort c m (list.reverse ss ++ acc_s) (list.reverse vs ++ acc_v)
    proof
        match (ss, vs)
            (s :: sr, v :: vr) ->
                have list.reverse_cons_append sr s acc_s
                have list.reverse_cons_append vr v acc_v
                have fields_reverse c m sr vr (s :: acc_s) (v :: acc_v)
            _                  ->
                have list.length_reverse ss
                have list.length_reverse vs

lemma fields_nth c m ss vs j : c~Context, m~Model, ss~List Sort, vs~List Value, j~Nat, fields_of_sort c m ss vs
    ensures match list.head (list.drop j ss)
        Some s ->
            match list.head (list.drop j vs)
                Some x -> of_sort c m s x
                None   -> False
        None   -> True
    proof
        match (ss, vs)
            (_ :: sr, _ :: vr) ->
                match j
                    0 -> auto
                    _ -> have fields_nth c m sr vr (j - 1)
            _                  -> auto

lemma field_sort_nth args fs j : args~List Sort, fs~List term.Field, j~Nat
    ensures match list.head (list.drop j fs)
        Some f -> list.head (list.drop j (list.map (term.instantiate args) (term.field_sorts fs))) == Some (term.instantiate args f.sort)
        None   -> True
    proof
        match fs
            []        -> auto
            _ :: rest ->
                match j
                    0 -> auto
                    _ -> have field_sort_nth args rest (j - 1)

# The pieces of a `seq.++` whose arguments are sequences of `e`.
lemma concat_total c m e rs ss : c~Context, m~Model, e~Sort, rs~List (Result Value Unknown), ss~List Sort,
                                 results_of_sorts c m rs ss, list.all (\s -> s == Seq e) ss
    ensures match concat_all rs
        Ok xs -> all_of_sort c m e xs
        Err _ -> False
    proof
        match (rs, ss)
            (Ok (Sequence ys) :: rr, _ :: sr) ->
                have concat_total c m e rr sr
                match concat_all rr
                    Ok zs -> have all_of_sort_append c m e ys zs
            (_ :: rr, _ :: sr)                -> have concat_total c m e rr sr
            _                                 -> auto

# Whether each of `ts` has the sort in the same place of `ss`.
fn sorted_each sig senv ts ss -> r : sig~Sig, senv~List Sort, ts~List Term, ss~List Sort, r~Bool
    match (ts, ss)
        ([], [])           -> True
        (t :: tr, s :: sr) -> term.sort_of sig senv t == Ok s and sorted_each sig senv tr sr
        _                  -> False

lemma sorts_of_each sig senv ts ss : sig~Sig, senv~List Sort, ts~List Term, ss~List Sort, term.sorts_of sig senv ts == Ok ss
    ensures sorted_each sig senv ts ss
    proof
        match ts
            []        -> have term.sorts_of_nil sig senv
            t :: rest ->
                have term.sorts_of_cons sig senv t rest
                match (term.sort_of sig senv t, term.sorts_of sig senv rest)
                    (Ok _, Ok more) -> have sorts_of_each sig senv rest more

# In a total model (`total`, `arrays_total`), every term of the context
# whose variables have values of their sorts has a value of its sort.
lemma value_total low c m env senv t s : low~Lower, c~Context, m~Model, env~List (Result Value Unknown), senv~List Sort,
                                         t~Term, s~Sort, results_of_sorts c m env senv,
                                         term.sorts_ok (term.signature c) 0 senv,
                                         term.sort_of (term.signature c) senv t == Ok s,
                                         total: forall r : r~Read, gives c m r,
                                         arrays_total: forall s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2 : s2~Sort, a2~Nat, b2~Nat, i2~Value, j2~Value, x2~Value,
                                         vs2~List Value, ss2~List Sort, xs2~Sort, body2~Term,
                                         arrays_total_at c m s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2
    ensures result_of_sort c m s (value low AsGiven c m env senv t)
    proof
        let sig = term.signature c
        match t
            Var i          ->
                have term.sort_of_var sig senv i
                have results_nth c m env senv i
            App h args     ->
                have term.sort_of_app sig senv h args
                match term.sorts_of sig senv args
                    Ok found -> have apply_total low c m env senv t h args s found
            Let binds body ->
                have term.sort_of_let sig senv binds body
                match term.sorts_of sig senv (term.bind_terms binds)
                    Ok ss ->
                        have sorts_of_each sig senv (term.bind_terms binds) ss
                        have term.sorts_of_ok c senv (term.bind_terms binds) ss
                        have term.sorts_ok_reverse_append sig ss senv
                        have bound_total low c m env senv binds ss
                        let rs = bound low AsGiven c m env senv binds
                        have results_reverse c m rs ss env senv
                        have value_total low c m (list.reverse rs ++ env) (list.reverse ss ++ senv) body s
            Lam x xs body  ->
                have term.sort_of_lam sig senv x xs body
                have term.sort_of_lam sig senv b"x" xs body
                have term.sort_of_ok c senv t s
                have all_known_total c m env senv
                match (all_known env, term.sort_of sig (xs :: senv) body)
                    (Ok vs, Ok _) ->
                        have fields_reverse c m senv vs [] []
                        have list.append_nil (list.reverse senv)
                        have list.append_nil (list.reverse vs)
                        have arrays_total s 0 0 (Truth True) (Truth True) (Truth True) vs senv xs body

lemma apply_total low c m env senv t h args s found : low~Lower, c~Context, m~Model, env~List (Result Value Unknown),
                                                      senv~List Sort, t~Term, h~Head, args~List Term, s~Sort,
                                                      found~List Sort, t == App h args, results_of_sorts c m env senv,
                                                      term.sorts_ok (term.signature c) 0 senv,
                                                      term.sort_of (term.signature c) senv t == Ok s,
                                                      term.sorts_of (term.signature c) senv args == Ok found,
                                                      term.apply_sort (term.signature c) h found == Ok s,
                                                      total: forall r : r~Read, gives c m r,
                                                      arrays_total: forall s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2 : s2~Sort, a2~Nat, b2~Nat, i2~Value, j2~Value, x2~Value,
                                                      vs2~List Value, ss2~List Sort, xs2~Sort, body2~Term,
                                                      arrays_total_at c m s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2
    ensures result_of_sort c m s (apply low AsGiven c m env senv t h args)
    proof
        let sig = term.signature c
        have sorts_of_each sig senv args found
        have term.sorts_of_ok c senv args found
        have values_total low c m env senv args found
        let rs = values low AsGiven c m env senv args
        have all_known_total c m rs found
        match h
            Prim op       -> have prim_total low c m env senv t op args s found
            Num n         -> have term.apply_num sig n found
            Boolean b     -> have term.apply_boolean sig b found
            EmptySeq e    -> have term.apply_empty_seq sig e found
            ConstArr a    ->
                have term.apply_const_arr sig a found
                match rs
                    [Ok x] -> have arrays_total a 0 0 x x x [] [] Bool (Var 0)
                    _      -> auto
            Con d k cargs ->
                have term.apply_con sig d k cargs found
                have s == Data d cargs
            Is d k        -> have term.apply_is sig d k found
            Sel d k j     ->
                have term.apply_sel sig d k j found
                match (args, rs, found, term.ctor sig d k)
                    ([a], [Ok (Constructed l fs)], [Data _ sargs], Some kc) ->
                        match term.ctor sig d l
                            Some kl ->
                                have fields_nth c m (list.map (term.instantiate sargs) (term.field_sorts kl.fields)) fs j
                                have field_sort_nth sargs kl.fields j
                                have term.sort_of_ok c senv a (Data d sargs)
                                have total (WrongSelAt d k j sargs (Constructed l fs))
                            None    -> auto
                    _                                                       -> auto
            Fun f         ->
                have term.apply_fun sig f found
                match all_known rs
                    Ok vs -> have total (FunAt f vs)

lemma prim_total low c m env senv t op args s found : low~Lower, c~Context, m~Model, env~List (Result Value Unknown),
                                                      senv~List Sort, t~Term, op~Op, args~List Term, s~Sort,
                                                      found~List Sort, t == App (Prim op) args,
                                                      results_of_sorts c m env senv,
                                                      term.sorts_ok (term.signature c) 0 senv,
                                                      term.sort_of (term.signature c) senv t == Ok s,
                                                      sorted_each (term.signature c) senv args found,
                                                      term.sorts_ok (term.signature c) 0 found,
                                                      term.apply_sort (term.signature c) (Prim op) found == Ok s,
                                                      total: forall r : r~Read, gives c m r,
                                                      arrays_total: forall s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2 : s2~Sort, a2~Nat, b2~Nat, i2~Value, j2~Value, x2~Value,
                                                      vs2~List Value, ss2~List Sort, xs2~Sort, body2~Term,
                                                      arrays_total_at c m s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2
    ensures result_of_sort c m s (prim low AsGiven c m env senv t op args)
    proof
        let sig = term.signature c
        have term.apply_prim sig op found
        have values_total low c m env senv args found
        match (op, args, found)
            (And, _, _)                            -> have conj_total low c m env senv args found
            (Or, _, _)                             -> have disj_total low c m env senv args found
            (SeqConcat, _, Seq e :: _)             -> have concat_total c m e (values low AsGiven c m env senv args) found
            (Div, [a, b], _)                       ->
                match value low AsGiven c m env senv a
                    Ok (Integer x) -> have total (DivZeroAt x)
                    _              -> auto
            (Mod, [a, b], _)                       ->
                match value low AsGiven c m env senv a
                    Ok (Integer x) -> have total (ModZeroAt x)
                    _              -> auto
            (Select, [a, i], [sa, _])              ->
                have term.sort_of_ok c senv a sa
                match (value low AsGiven c m env senv a, value low AsGiven c m env senv i)
                    (Ok (ArrayElem k), Ok j) -> have arrays_total sa k k j j j [] [] Bool (Var 0)
                    _                        -> auto
            (Store, [a, i, v], [sa, _, _])         ->
                have term.sort_of_ok c senv a sa
                match (value low AsGiven c m env senv a, value low AsGiven c m env senv i, value low AsGiven c m env senv v)
                    (Ok (ArrayElem k), Ok j, Ok x) -> have arrays_total sa k k j j x [] [] Bool (Var 0)
                    _                              -> auto
            (MapAdd, [a, b], [sa, _])              ->
                have term.sort_of_ok c senv a sa
                match (value low AsGiven c m env senv a, value low AsGiven c m env senv b)
                    (Ok (ArrayElem p), Ok (ArrayElem q)) -> have arrays_total s p q (Integer 0) (Integer 0) (Integer 0) [] [] Bool (Var 0)
                    _                                    -> auto
            (SeqNth, [a, i], [Seq e, _])           ->
                match (value low AsGiven c m env senv a, value low AsGiven c m env senv i)
                    (Ok (Sequence xs), Ok (Integer n)) ->
                        if 0 <= n and n < list.length xs
                            have all_of_sort_nth c m e xs n
                        else
                            have total (NthOutAt e xs n)
                    _                                  -> auto
            (SeqExtract, [a, i, n], [Seq e, _, _]) ->
                match (value low AsGiven c m env senv a, value low AsGiven c m env senv i, value low AsGiven c m env senv n)
                    (Ok (Sequence xs), Ok (Integer from), Ok (Integer count)) ->
                        if 0 <= from and from < list.length xs and 0 < count
                            have all_of_sort_drop c m e from xs
                            have all_of_sort_take c m e count (list.drop from xs)
                        else
                            auto
                    _                                                         -> auto
            _                                      -> auto

lemma values_total low c m env senv ts ss : low~Lower, c~Context, m~Model, env~List (Result Value Unknown), senv~List Sort,
                                            ts~List Term, ss~List Sort, results_of_sorts c m env senv,
                                            term.sorts_ok (term.signature c) 0 senv,
                                            sorted_each (term.signature c) senv ts ss,
                                            total: forall r : r~Read, gives c m r,
                                            arrays_total: forall s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2 : s2~Sort, a2~Nat, b2~Nat, i2~Value, j2~Value, x2~Value,
                                            vs2~List Value, ss2~List Sort, xs2~Sort, body2~Term,
                                            arrays_total_at c m s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2
    ensures results_of_sorts c m (values low AsGiven c m env senv ts) ss
    proof
        match (ts, ss)
            (t :: tr, s :: sr) ->
                have value_total low c m env senv t s
                have values_total low c m env senv tr sr
            _                  -> auto

lemma bound_total low c m env senv bs ss : low~Lower, c~Context, m~Model, env~List (Result Value Unknown), senv~List Sort,
                                           bs~List (Name, Term), ss~List Sort, results_of_sorts c m env senv,
                                           term.sorts_ok (term.signature c) 0 senv,
                                           sorted_each (term.signature c) senv (term.bind_terms bs) ss,
                                           total: forall r : r~Read, gives c m r,
                                           arrays_total: forall s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2 : s2~Sort, a2~Nat, b2~Nat, i2~Value, j2~Value, x2~Value,
                                           vs2~List Value, ss2~List Sort, xs2~Sort, body2~Term,
                                           arrays_total_at c m s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2
    ensures results_of_sorts c m (bound low AsGiven c m env senv bs) ss
    proof
        match (bs, ss)
            ((_, t) :: rest, s :: sr) ->
                have value_total low c m env senv t s
                have bound_total low c m env senv rest sr
            _                         -> auto

lemma conj_total low c m env senv ts ss : low~Lower, c~Context, m~Model, env~List (Result Value Unknown), senv~List Sort,
                                          ts~List Term, ss~List Sort, results_of_sorts c m env senv,
                                          term.sorts_ok (term.signature c) 0 senv,
                                          sorted_each (term.signature c) senv ts ss, list.all (\x -> x == Bool) ss,
                                          total: forall r : r~Read, gives c m r,
                                          arrays_total: forall s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2 : s2~Sort, a2~Nat, b2~Nat, i2~Value, j2~Value, x2~Value,
                                          vs2~List Value, ss2~List Sort, xs2~Sort, body2~Term,
                                          arrays_total_at c m s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2
    ensures match conj low AsGiven c m env senv ts
        Ok _  -> True
        Err _ -> False
    proof
        match (ts, ss)
            (t :: tr, s :: sr) ->
                have value_total low c m env senv t s
                have conj_total low c m env senv tr sr
            _                  -> auto

lemma disj_total low c m env senv ts ss : low~Lower, c~Context, m~Model, env~List (Result Value Unknown), senv~List Sort,
                                          ts~List Term, ss~List Sort, results_of_sorts c m env senv,
                                          term.sorts_ok (term.signature c) 0 senv,
                                          sorted_each (term.signature c) senv ts ss, list.all (\x -> x == Bool) ss,
                                          total: forall r : r~Read, gives c m r,
                                          arrays_total: forall s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2 : s2~Sort, a2~Nat, b2~Nat, i2~Value, j2~Value, x2~Value,
                                          vs2~List Value, ss2~List Sort, xs2~Sort, body2~Term,
                                          arrays_total_at c m s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2
    ensures match disj low AsGiven c m env senv ts
        Ok _  -> True
        Err _ -> False
    proof
        match (ts, ss)
            (t :: tr, s :: sr) ->
                have value_total low c m env senv t s
                have disj_total low c m env senv tr sr
            _                  -> auto

# In a model that answers every read (`gives`) and every array question
# (`arrays_total_at`), every closed term of the context has a value, of its
# sort. The array laws and the definitions' equations are not assumed or
# concluded: this is about values existing, not about what they are.
export lemma total_has_value c m t s : c~Context, m~Model, t~Term, s~Sort, term.sort_of (term.signature c) [] t == Ok s,
                                       total: forall r : r~Read, gives c m r,
                                       arrays_total: forall s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2 : s2~Sort, a2~Nat, b2~Nat, i2~Value, j2~Value, x2~Value,
                                       vs2~List Value, ss2~List Sort, xs2~Sort, body2~Term,
                                       arrays_total_at c m s2 a2 b2 i2 j2 x2 vs2 ss2 xs2 body2
    ensures has_value c m t
    proof
        have value_total (level AsGiven c m m.fuel) c m [] [] t s
        have eval c m t == value (level AsGiven c m m.fuel) AsGiven c m [] [] t

# What `has_value` is, for other modules (its body is sealed there).
export lemma has_value_def c m t : c~Context, m~Model, t~Term
    ensures has_value c m t
        == match (term.sort_of (term.signature c) [] t, eval c m t)
            (Ok s, Ok v) -> of_sort c m s v
            _            -> False

# ── Every definition's equation is an axiom of the context ───────────────────

# The parameters of a binder list, `Var (k - 1)` … `Var 0`, have its sorts,
# in order.
lemma params_sorted sig ss e : sig~Sig, ss~List Sort, e~List Sort
    ensures term.sorts_of sig (list.reverse ss ++ e) (params_from (list.length ss)) == Ok ss
    proof
        match ss
            []        -> have term.sorts_of_nil sig e
            x :: rest ->
                let env = list.reverse rest ++ (x :: e)
                have list.reverse_cons_append rest x e
                have list.length_reverse rest
                have list.drop_append (list.reverse rest) (x :: e)
                have term.sort_of_var sig env (list.length rest)
                have params_sorted sig rest (x :: e)
                have term.sorts_of_cons sig env (Var (list.length rest)) (params_from (list.length rest))

# The equation of a definition of `c` is well-sorted in `c`: `holds_at`
# asks it at values, and is false of an axiom that isn't.
export lemma definition_axiom_ok c n d : c~Context, n~Nat, d~Def, list.contains (term.defs c) (n, d)
    ensures term.axiom_ok c (definition_axiom n d)
    proof
        let sig = term.signature c
        let env = term.binder_env d.params
        let ss = term.var_sorts d.params
        let ps = params_from (list.length d.params)
        let lhs = App (Fun n) ps
        have term.def_of_context c n d
        have term.def_ok_def c n d
        have term.def_fun_params d
        have term.axiom_ok_def c (definition_axiom n d)
        have term.binder_env_def d.params
        have term.var_sorts_length d.params
        have params_sorted sig ss []
        have list.append_nil (list.reverse ss)
        have term.check_term_def sig env d.body d.result
        have term.check_term_def sig env (App (Prim Eq) [lhs, d.body]) Bool
        have term.sort_of_app sig env (Prim Eq) [lhs, d.body]
        have term.sorts_of_cons sig env lhs [d.body]
        have term.sorts_of_cons sig env d.body []
        have term.sorts_of_nil sig env
        have term.sort_of_app sig env (Fun n) ps
        have term.apply_fun sig n ss
        have term.apply_prim sig Eq [d.result, d.result]

# Every definition's equation is an axiom of the context, all at once.
export lemma definitions_ok c : c~Context
    ensures forall n d : n~Nat, d~Def, list.contains (term.defs c) (n, d), term.axiom_ok c (definition_axiom n d)
    proof
        have definition_axiom_ok c n d

# ── `before` is a strict total order ─────────────────────────────────────────
# What normal forms rest on (#308's reading, owed by S6): `before` never
# holds of a value and itself, chains, and orders every two different
# values. `before` is private, and so are these: they are for this
# module's proofs about normal forms.

lemma before_irreflexive a : a~Value
    ensures not (before a a)
    proof
        match a
            Sequence xs      -> have all_before_irreflexive xs
            Constructed _ xs -> have all_before_irreflexive xs
            _                -> auto

lemma all_before_irreflexive xs : xs~List Value
    ensures not (all_before xs xs)
    proof
        match xs
            []        -> auto
            x :: rest ->
                have before_irreflexive x
                have all_before_irreflexive rest

lemma before_transitive a b d : a~Value, b~Value, d~Value, before a b, before b d
    ensures before a d
    proof
        match (a, b, d)
            (Sequence xs, Sequence ys, Sequence zs)                -> have all_before_transitive xs ys zs
            (Constructed k xs, Constructed l ys, Constructed j zs) ->
                if k == l and l == j then have all_before_transitive xs ys zs else auto
            _                                                      -> auto

lemma all_before_transitive xs ys zs : xs~List Value, ys~List Value, zs~List Value, all_before xs ys, all_before ys zs
    ensures all_before xs zs
    proof
        match (xs, ys, zs)
            (x :: xr, y :: yr, z :: zr) ->
                if before x y and before y z
                    have before_transitive x y z
                else if x == y and y == z
                    have all_before_transitive xr yr zr
                else
                    auto
            _                           -> auto

lemma before_total a b : a~Value, b~Value, a != b
    ensures before a b or before b a
    proof
        match (a, b)
            (Sequence xs, Sequence ys)           -> have all_before_total xs ys
            (Constructed _ xs, Constructed _ ys) -> if xs != ys then have all_before_total xs ys else auto
            _                                    -> auto

lemma all_before_total xs ys : xs~List Value, ys~List Value, xs != ys
    ensures all_before xs ys or all_before ys xs
    proof
        match (xs, ys)
            (x :: xr, y :: yr) -> if x == y then have all_before_total xr yr else have before_total x y
            _                  -> auto
