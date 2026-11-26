# smtlib.ck — SMT-LIB text in and out, for the subset `ckc` writes
# (SPEC §7.3): `parse` reads a query into a `Query`, `render` writes one.
#
# A query is options, `(set-logic …)`, commands that build a `Context`, the
# goal asserted negated, `(check-sat)`, and optionally `(get-unsat-core)`
# and `(get-value …)`, in that order.
# Anything outside the subset is an `Error` that says where and what.
#
# `render (parse q)` is `q` again, except for white space and comments
# (one space between tokens, one command per line) and one spelling: a
# constructor is always written `(as C S)`, also where `q` wrote `C` alone.

module smtlib

import std.array
import std.bytes
import std.list
import std.parse (Parsable)
import std.string
import term (Name, Sort, Bool, Int, Seq, Arr, Data, Unin, Param, SortDecl, Field, Ctor, Datatype)
import term (FunKind, Declared, Constant, Defined, FunDecl)
import term (Op, Not, And, Or, Implies, Ite, Eq, Add, Sub, Neg, Mul, Div, Mod, Lt, Le, Gt, Ge, Select, Store, MapAdd)
import term (SeqLen, SeqNth, SeqUnit, SeqConcat, SeqExtract)
import term (Head, Fun, Con, Is, Sel, Num, Boolean, Prim, ConstArr, EmptySeq, Term, Var, App, Let, Lam)
import term (Def, DefKind, Recursive, Plain, Axiom, Command, DeclareSort, DeclareDatatypes, DeclareFun, DefineFuns, Assume)
import term (Assert)
import term (Sig, Context, Problem, BadSort, NoCtors, BadApply, Unbound, EmptyLet, ConstantParams, Expected, NoPattern)
import term (NotWellFounded, NoBaseCase, NotCovariant)
import term (NamedTwice, PlainInGroup)
import reserved

# ── Errors ───────────────────────────────────────────────────────────────────

# What went wrong, and where in `src` (a byte offset).
export record Error src : src~ghost Bytes
    pos~Nat, pos <= len src
    message~Bytes

# The line and column of byte `pos`, both from 1; columns count bytes.
export fn position src pos -> r : src~Bytes, pos~Nat, r~((l~Nat, l >= 1), (c~Nat, c >= 1))
    count_lines src 0 pos 1 1

fn count_lines src i pos line col -> r : src~Bytes, i~Nat, i <= len src, pos~Nat, line~Nat, line >= 1, col~Nat, col >= 1,
                                         r~((l~Nat, l >= 1), (c~Nat, c >= 1))
    decreasing len src - i
    if i < pos and i < len src
        if src[i] == '\n' then count_lines src (i + 1) pos (line + 1) 1 else count_lines src (i + 1) pos line (col + 1)
    else
        (line, col)

# The error as Z3 reports one: `line L column C: message`.
export fn describe src e -> r : src~Bytes, e~Error src, r~Bytes
    let (line, col) = position src e.pos
    b"line " ++ numeral line ++ b" column " ++ numeral col ++ b": " ++ e.message

# ── Reading S-expressions ────────────────────────────────────────────────────

# A token that isn't a parenthesis. A symbol's text is without its bars,
# if it was written with them (`quoted`).
export enum Atom
    Symbol text quoted : text~Bytes, quoted~Bool
    Keyword text       : text~Bytes
    Numeral n          : n~Nat

# An S-expression of `src`, with the offset where it starts.
export enum SExpr src : src~ghost Bytes
    Leaf a at     : a~Atom, at~Nat, at < len src
    Node items at : items~List (SExpr src), at~Nat, at < len src

# A value read from `src` starting at `start`, and where it stopped.
record Parsed a src start : a~Type, src~Bytes, start~Nat
    value~a
    stop~Nat, start < stop, stop <= len src

fn is_space b : b~U8
    b == ' ' or b == '\t' or b == '\n' or b == '\r'

fn is_digit b : b~U8
    '0' <= b and b <= '9'

# A character of a simple symbol (SMT-LIB 2.6, §3.1).
fn symbol_byte b : b~U8
    ('a' <= b and b <= 'z') or ('A' <= b and b <= 'Z') or is_digit b or b == '~' or b == '!' or b == '@'
        or b == '$' or b == '%' or b == '^' or b == '&' or b == '*' or b == '_' or b == '-' or b == '+'
        or b == '=' or b == '<' or b == '>' or b == '.' or b == '?' or b == '/'

# White space and comments skipped.
fn skip src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i >= len src
        i
    else if src[i] == ';'
        skip_comment src (i + 1)
    else if is_space src[i]
        skip src (i + 1)
    else
        i

fn skip_comment src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i >= len src
        i
    else if src[i] == '\n'
        skip src (i + 1)
    else
        skip_comment src (i + 1)

fn symbol_end src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i < len src and symbol_byte src[i] then symbol_end src (i + 1) else i

# Where the quoted symbol whose text starts at `i` ends: the offset of its
# closing `|`, or an error at an unexpected `\`.
fn quoted_end src start i -> r : src~Bytes, start~Nat, start < i, i <= len src,
                                 r~Result (j~Nat, i <= j, j < len src) (Error src)
    decreasing len src - i
    if i >= len src
        Err (Error start b"this `|` is never closed")
    else if src[i] == '|'
        Ok i
    else if src[i] == '\\'
        Err (Error i b"a `\\` in a quoted symbol is outside the subset `ckc` writes")
    else
        quoted_end src start (i + 1)

# One S-expression starting at `i`, which isn't white space.
fn expr src i -> r : src~Bytes, i~Nat, i < len src, r~Result (Parsed (SExpr src) src i) (Error src)
    decreasing (len src - i, 0)
    let b = src[i]
    if b == '('
        items src i (i + 1) []
    else if b == ')'
        Err (Error i b"unexpected `)`")
    else if b == '|'
        let j = try quoted_end src i (i + 1)
        if j == i + 1
            Err (Error i b"the empty symbol `||` is outside the subset `ckc` writes")
        else
            Ok (Parsed (Leaf (Symbol (bytes.slice src (i + 1) j) True) i) (j + 1))
    else if b == ':'
        let j = symbol_end src (i + 1)
        if j == i + 1
            Err (Error i b"expected a keyword after `:`")
        else
            Ok (Parsed (Leaf (Keyword (bytes.slice src (i + 1) j)) i) j)
    else if is_digit b
        let ds = bytes.slice src i (len src)
        have bytes.slice_at src i (len src) 0
        have string.parse_digits ds
        match Parsable.parse ds Int Int
            Ok (n, after) ->
                let j = len src - len after
                if j < len src and (symbol_byte src[j] or src[j] == '|')
                    Err (Error i b"only whole numbers are in the subset `ckc` writes")
                else if b == '0' and j > i + 1
                    Err (Error i b"a numeral other than `0` can't start with `0`")
                else
                    Ok (Parsed (Leaf (Numeral n) i) j)
    else if b == '-' and i + 1 < len src and is_digit src[i + 1]
        # Z3 reads `-` and a digit as the start of a number, never of a symbol.
        Err (Error i b"a negative numeral is outside the subset `ckc` writes: write `(- N)`")
    else if symbol_byte b
        let j = symbol_end src (i + 1)
        Ok (Parsed (Leaf (Symbol (bytes.slice src i j) False) i) j)
    else if b == '"'
        Err (Error i b"string literals are outside the subset `ckc` writes")
    else if b == '#'
        Err (Error i b"`#` literals are outside the subset `ckc` writes")
    else
        Err (Error i b"unexpected character")

# The rest of a list opened at `start`, from `k`.
fn items src start k acc -> r : src~Bytes, start~Nat, k~Nat, start < k, k <= len src,
                                acc~List (SExpr src), r~Result (Parsed (SExpr src) src start) (Error src)
    decreasing (len src - k, 1)
    let j = skip src k
    if j >= len src
        Err (Error start b"this `(` is never closed")
    else if src[j] == ')'
        Ok (Parsed (Node (list.reverse acc) start) (j + 1))
    else
        let e = try expr src j
        items src start e.stop (e.value :: acc)

# Where the S-expression starting at `i` ends: the offset just after it.
export fn end_of src i -> r : src~Bytes, i~Nat, i < len src, r~Result (j~Nat, i < j, j <= len src) (Error src)
    let e = try expr src i
    Ok e.stop

# Every S-expression in `src`, in order.
export fn read src -> r : src~Bytes, r~Result (List (SExpr src)) (Error src)
    read_from src 0 []

fn read_from src i acc -> r : src~Bytes, i~Nat, i <= len src, acc~List (SExpr src),
                              r~Result (List (SExpr src)) (Error src)
    decreasing len src - i
    let j = skip src i
    if j >= len src
        Ok (list.reverse acc)
    else
        let e = try expr src j
        read_from src e.stop (e.value :: acc)

# ── Queries ──────────────────────────────────────────────────────────────────

# `(set-option :key value)`.
export record Opt
    key~Bytes
    value~Atom

# A query: options, the logic, the context, and the goal, which the query
# asserts negated: it asks whether the goal follows from the context.
# `core` is whether `(get-unsat-core)` follows `(check-sat)`, and `values`
# are the terms `(get-value …)` asks for after it, if it does.
#
# `goal_at` is how many of the context's commands came before the negated
# goal; the assertions after it are facts of the context like any other.
# Only `render` reads it, to write the goal back where it was. It carries no
# meaning: the assertions are a conjunction, so their order doesn't matter,
# and the goal is a fact of the whole context.
export record Query
    options~List Opt
    logic~Name
    context~Context
    goal~Term, term.fact_ok context goal
    goal_at~Nat, goal_at <= list.length (term.commands context)
    core~Bool
    values~Option (List Term), values_ok context values

export fn values_ok c vs -> r : c~Context, vs~Option (List Term), r~Bool
    match vs
        None    -> True
        Some ts -> term.terms_ok c ts

# ── Names in a signature ─────────────────────────────────────────────────────

fn find_fun funs name i -> r : funs~Array FunDecl, name~Name, i~Nat, i <= len funs, r~Option Nat
    decreasing len funs - i
    if i >= len funs then None else if funs[i].name == name then Some i else find_fun funs name (i + 1)

fn find_sort sorts name i -> r : sorts~Array SortDecl, name~Name, i~Nat, i <= len sorts, r~Option Nat
    decreasing len sorts - i
    if i >= len sorts then None else if sorts[i].name == name then Some i else find_sort sorts name (i + 1)

fn find_datatype dts name i -> r : dts~Array Datatype, name~Name, i~Nat, i <= len dts, r~Option Nat
    decreasing len dts - i
    if i >= len dts then None else if dts[i].name == name then Some i else find_datatype dts name (i + 1)

fn ctor_index cs name k -> r : cs~List Ctor, name~Name, k~Nat, r~Option Nat
    match cs
        []        -> None
        c :: rest -> if c.name == name then Some k else ctor_index rest name (k + 1)

# The datatype and constructor named `name`.
fn find_ctor dts name d -> r : dts~Array Datatype, name~Name, d~Nat, d <= len dts, r~Option (Nat, Nat)
    decreasing len dts - d
    if d >= len dts
        None
    else
        match ctor_index dts[d].ctors name 0
            Some k -> Some (d, k)
            None   -> find_ctor dts name (d + 1)

fn field_index fs name j -> r : fs~List Field, name~Name, j~Nat, r~Option Nat
    match fs
        []        -> None
        f :: rest -> if f.name == name then Some j else field_index rest name (j + 1)

fn sel_in cs name k -> r : cs~List Ctor, name~Name, k~Nat, r~Option (Nat, Nat)
    match cs
        []        -> None
        c :: rest ->
            match field_index c.fields name 0
                Some j -> Some (k, j)
                None   -> sel_in rest name (k + 1)

# The datatype, constructor and field of the selector named `name`.
fn find_sel dts name d -> r : dts~Array Datatype, name~Name, d~Nat, d <= len dts, r~Option (Nat, Nat, Nat)
    decreasing len dts - d
    if d >= len dts
        None
    else
        match sel_in dts[d].ctors name 0
            Some (k, j) -> Some (d, k, j)
            None        -> find_sel dts name (d + 1)

fn name_index ns name i -> r : ns~List Name, name~Name, i~Nat, r~Option Nat
    match ns
        []        -> None
        n :: rest -> if n == name then Some i else name_index rest name (i + 1)

# A constructor's tester: `is-` and its name.
export fn tester_name c -> r : c~Name, r~Name
    b"is-" ++ c

fn tester_of dts name -> r : dts~Array Datatype, name~Name, r~Option (Nat, Nat)
    if len name > 3 and bytes.matches_at name 0 b"is-"
        find_ctor dts (bytes.slice name 3 (len name)) 0
    else
        None

# How SMT-LIB writes each built-in operation (`-` is `Sub` with two
# arguments, `Neg` with one).
export fn op_text op -> r : op~Op, r~Bytes
    match op
        Not        -> b"not"
        And        -> b"and"
        Or         -> b"or"
        Implies    -> b"=>"
        Ite        -> b"ite"
        Eq         -> b"="
        Add        -> b"+"
        Sub        -> b"-"
        Neg        -> b"-"
        Mul        -> b"*"
        Div        -> b"div"
        Mod        -> b"mod"
        Lt         -> b"<"
        Le         -> b"<="
        Gt         -> b">"
        Ge         -> b">="
        Select     -> b"select"
        Store      -> b"store"
        MapAdd     -> b"(_ map (+ (Int Int) Int))"
        SeqLen     -> b"seq.len"
        SeqNth     -> b"seq.nth"
        SeqUnit    -> b"seq.unit"
        SeqConcat  -> b"seq.++"
        SeqExtract -> b"seq.extract"

# The operations a name alone can denote (`Neg` is `-` with one argument;
# `MapAdd` is written `(_ map …)`).
let NAMED = [Eq, Not, And, Or, Implies, Ite, Add, Sub, Mul, Div, Mod, Lt, Le, Gt, Ge, Select, Store, SeqLen, SeqNth,
             SeqUnit, SeqConcat, SeqExtract]

fn find_prim ops name -> r : ops~List Op, name~Name, r~Option Op
    match ops
        []        -> None
        o :: rest -> if op_text o == name then Some o else find_prim rest name

# The built-in operation named `name`, given `n` arguments.
fn prim_op name n -> r : name~Name, n~Nat, r~Option Op
    if name == b"-" and n == 1 then Some Neg else find_prim NAMED name

# Names SMT-LIB or Z3 define that the subset leaves out.
fn outside name -> r : name~Name, r~Bool
    name == b"xor" or name == b"distinct" or name == b"exists" or name == b"abs"
        or name == b"/" or name == b"to_real" or name == b"to_int" or name == b"match"
        or name == b"declare-datatype" or name == b"push" or name == b"pop"
        or name == b"check-sat-assuming" or name == b"get-model" or name == b"exit"

# Words with a meaning of their own, which can't name anything.
fn keyword name -> r : name~Name, r~Bool
    name == b"let" or name == b"lambda" or name == b"forall" or name == b"exists" or name == b"!"
        or name == b"_" or name == b"as" or name == b"par" or name == b"match" or name == b"true"
        or name == b"false" or name == b"Int" or name == b"Bool" or name == b"Seq" or name == b"Array"

# Whether a function-like name is taken: a built-in, a function, a
# constructor, a tester or a selector.
fn taken sig name -> r : sig~Sig, name~Name, r~Bool
    tester_like name or keyword name or reserved.is_reserved name or prim_op name 2 != None or outside name or find_fun sig.funs name 0 != None
        or find_ctor sig.datatypes name 0 != None or tester_of sig.datatypes name != None
        or find_sel sig.datatypes name 0 != None

fn sort_taken sig name -> r : sig~Sig, name~Name, r~Bool
    tester_like name or keyword name or reserved.is_reserved name or find_sort sig.sorts name 0 != None or find_datatype sig.datatypes name 0 != None

# Whether `name` is spelled `is-…`, as a tester is: nothing a query
# introduces is, so that a tester's spelling has no other meaning (Z3 reads
# `is-` as the tester of a constructor `||`).
fn tester_like name -> r : name~Name, r~Bool
    len name >= 3 and bytes.matches_at name 0 b"is-"

# `name`, as written in a message.
fn shown name -> r : name~Name, r~Bytes
    b"`" ++ name ++ b"`"

# ── Sorts ────────────────────────────────────────────────────────────────────

# The sort `e` denotes, where `params` are a datatype's parameters.
fn sort_from src sig params e -> r : src~Bytes, sig~Sig, params~List Name, e~SExpr src, r~Result Sort (Error src)
    match e
        Leaf (Symbol n _) p                  ->
            match name_index params n 0
                Some k -> Ok (Param k)
                None   ->
                    if n == b"Int" then Ok Int else if n == b"Bool" then Ok Bool else named_sort src sig n [] p
        Node (Leaf (Symbol n _) p :: args) _ ->
            if n == b"_"
                Err (Error p b"indexed sorts are outside the subset `ckc` writes")
            else if n == b"Seq"
                match args
                    [a] ->
                        let s = try sort_from src sig params a
                        Ok (Seq s)
                    _   -> Err (Error p b"`Seq` takes one sort")
            else if n == b"Array"
                match args
                    [a, b] ->
                        let i = try sort_from src sig params a
                        let v = try sort_from src sig params b
                        Ok (Arr i v)
                    _      -> Err (Error p b"`Array` takes two sorts here: arrays of more than one index are outside the subset `ckc` writes")
            else
                let ss = try sorts_from src sig params args
                named_sort src sig n ss p
        Leaf _ p                             -> Err (Error p b"expected a sort")
        Node _ p                             -> Err (Error p b"expected a sort")

fn sorts_from src sig params es -> r : src~Bytes, sig~Sig, params~List Name, es~List (SExpr src),
                                       r~Result (List Sort) (Error src)
    match es
        []        -> Ok []
        e :: rest ->
            let s = try sort_from src sig params e
            let ss = try sorts_from src sig params rest
            Ok (s :: ss)

# The declared sort or datatype `n` applied to `args`.
fn named_sort src sig n args p -> r : src~Bytes, sig~Sig, n~Name, args~List Sort, p~Nat, p < len src,
                                      r~Result Sort (Error src)
    match find_datatype sig.datatypes n 0
        Some d if d < len sig.datatypes ->
            let k = list.length sig.datatypes[d].params
            if list.length args == k then Ok (Data d args) else Err (Error p (arity_message n k))
        _ ->
            match find_sort sig.sorts n 0
                Some u if u < len sig.sorts ->
                    let k = sig.sorts[u].arity
                    if list.length args == k then Ok (Unin u args) else Err (Error p (arity_message n k))
                _ -> Err (Error p (b"unknown sort " ++ shown n))

fn arity_message n k -> r : n~Name, k~Nat, r~Bytes
    shown n ++ b" takes " ++ numeral k ++ (if k == 1 then b" sort" else b" sorts")

# ── Terms ────────────────────────────────────────────────────────────────────

# A term and its sort.
type Sorted = ts~(Term, Sort)

# The term `e` denotes, and its sort, where `vars` are the variables bound
# around it with their sorts (innermost first).
fn term_from src sig vars e -> r : src~Bytes, sig~Sig, vars~List (Name, Sort), e~SExpr src,
                                   r~Result Sorted (Error src)
    match e
        Leaf (Numeral n) _                                          -> Ok (App (Num n) [], Int)
        Leaf (Keyword _) p                                          -> Err (Error p b"expected a term, found a keyword")
        Leaf (Symbol n q) p                                         -> symbol_term src sig vars n q p
        Node [] p                                                   -> Err (Error p b"expected a term, found `()`")
        Node (Leaf (Symbol n False) hp :: args) p                   ->
            if n == b"let"
                let_term src sig vars args p
            else if n == b"lambda"
                lambda_term src sig vars args p
            else if n == b"forall" or n == b"exists"
                Err (Error hp (b"a quantifier is in the subset `ckc` writes only as a whole assertion, `(assert (forall …))`"))
            else if n == b"!"
                Err (Error hp b"`!` is in the subset `ckc` writes only around a `forall`'s body, or around an assertion to name it, `(assert (! TERM :named NAME))`")
            else if n == b"as"
                let h = try qualified_head src sig args p
                applied src sig h [] [] p
            else if n == b"_"
                Err (Error hp b"an indexed name is in the subset `ckc` writes only as `(_ map (+ (Int Int) Int))`")
            else
                named_apply src sig vars n hp args
        Node (Leaf (Symbol n True) hp :: args) _                    -> named_apply src sig vars n hp args
        Node [Node _ hp] _                                          -> Err (Error hp NO_ARGUMENTS)
        Node (Node (Leaf (Symbol q False) _ :: inner) hp :: args) _ ->
            if q == b"as"
                let h = try qualified_head src sig inner hp
                apply_to src sig vars h args hp
            else if q == b"_"
                if map_add inner
                    apply_to src sig vars (Prim MapAdd) args hp
                else
                    Err (Error hp b"an indexed name is in the subset `ckc` writes only as `(_ map (+ (Int Int) Int))`")
            else
                Err (Error hp b"expected a function's name")
        Node (_ :: _) p                                             -> Err (Error p b"expected a function's name at the start")

let NO_ARGUMENTS = b"an application needs arguments: a constant is written alone, without parentheses"

# The function named `n`, at `hp`, applied to the terms `args` write. A
# bound variable can't be applied: Z3 would read `(v t)` as `(select v t)`.
fn named_apply src sig vars n hp args -> r : src~Bytes, sig~Sig, vars~List (Name, Sort), n~Name, hp~Nat, hp < len src,
                                             args~List (SExpr src), r~Result Sorted (Error src)
    if var_index vars n 0 != None
        Err (Error hp (shown n ++ b" is a bound variable here, so it can't be applied to arguments"))
    else if args == []
        Err (Error hp NO_ARGUMENTS)
    else
        let h = try head_of src sig n hp (list.length args)
        apply_to src sig vars h args hp

# Head `h` (at `hp`) applied to the terms `args` write.
fn apply_to src sig vars h args hp -> r : src~Bytes, sig~Sig, vars~List (Name, Sort), h~Head, args~List (SExpr src),
                                          hp~Nat, hp < len src, r~Result Sorted (Error src)
    let (ts, ss) = try terms_from src sig vars args
    applied src sig h ts ss hp

fn terms_from src sig vars es -> r : src~Bytes, sig~Sig, vars~List (Name, Sort), es~List (SExpr src),
                                     r~Result (List Term, List Sort) (Error src)
    match es
        []        -> Ok ([], [])
        e :: rest ->
            let (t, s) = try term_from src sig vars e
            let (ts, ss) = try terms_from src sig vars rest
            Ok (t :: ts, s :: ss)

# `h` applied to `ts`, of sorts `ss`, with an error at `p` if it can't be.
fn applied src sig h ts ss p -> r : src~Bytes, sig~Sig, h~Head, ts~List Term, ss~List Sort, p~Nat, p < len src,
                                    r~Result Sorted (Error src)
    match term.apply_sort sig h ss
        Ok s   -> Ok (App h ts, s)
        Err pr -> Err (Error p (problem_message sig pr))

# Whether `es` is `map (+ (Int Int) Int)`, the inside of `(_ map …)`.
fn map_add es -> r : es~List (SExpr src), r~Bool
    match es
        [Leaf (Symbol m _) _, Node [Leaf (Symbol p _) _, Node [Leaf (Symbol a _) _, Leaf (Symbol b _) _] _, Leaf (Symbol c _) _] _] ->
            m == b"map" and p == b"+" and a == b"Int" and b == b"Int" and c == b"Int"
        _                                                                                                                           -> False

fn var_index vars n i -> r : vars~List (Name, Sort), n~Name, i~Nat, r~Option (Nat, Sort)
    match vars
        []             -> None
        (m, s) :: rest -> if m == n then Some (i, s) else var_index rest n (i + 1)

# A symbol alone: a variable, a constant, `true`, `false`, or a constructor
# without fields of a datatype without parameters.
fn symbol_term src sig vars n q p -> r : src~Bytes, sig~Sig, vars~List (Name, Sort), n~Name, q~Bool, p~Nat, p < len src,
                                         r~Result Sorted (Error src)
    match var_index vars n 0
        Some (i, s) -> Ok (Var i, s)
        None        ->
            if n == b"true" and not q
                Ok (App (Boolean True) [], Bool)
            else if n == b"false" and not q
                Ok (App (Boolean False) [], Bool)
            else
                let h = try head_of src sig n p 0
                applied src sig h [] [] p

# What the name `n` applies, given `k` arguments.
fn head_of src sig n p k -> r : src~Bytes, sig~Sig, n~Name, p~Nat, p < len src, k~Nat, r~Result Head (Error src)
    match prim_op n k
        Some op -> Ok (Prim op)
        None    ->
            match find_fun sig.funs n 0
                Some f -> Ok (Fun f)
                None   ->
                    match find_ctor sig.datatypes n 0
                        Some (d, c) ->
                            if d < len sig.datatypes and sig.datatypes[d].params == []
                                Ok (Con d c [])
                            else
                                Err (Error p (b"write " ++ shown n ++ b" as `(as " ++ n ++ b" SORT)`: its datatype has parameters"))
                        None        ->
                            match tester_of sig.datatypes n
                                Some (d, c) -> Ok (Is d c)
                                None        ->
                                    match find_sel sig.datatypes n 0
                                        Some (d, c, j) -> Ok (Sel d c j)
                                        None           ->
                                            if outside n
                                                Err (Error p (shown n ++ b" is outside the subset `ckc` writes"))
                                            else
                                                Err (Error p (b"unknown name " ++ shown n))

# The head `(as C S)`, `(as const S)` or `(as seq.empty S)` names, from what
# follows `as`.
fn qualified_head src sig args p -> r : src~Bytes, sig~Sig, args~List (SExpr src), p~Nat, p < len src,
                                        r~Result Head (Error src)
    match args
        [Leaf (Symbol c _) cp, s] ->
            let sort = try sort_from src sig [] s
            if c == b"const"
                Ok (ConstArr sort)
            else if c == b"seq.empty"
                Ok (EmptySeq sort)
            else
                match find_ctor sig.datatypes c 0
                    Some (d, k) ->
                        match sort
                            Data e sargs if e == d -> Ok (Con d k sargs)
                            _ -> Err (Error cp (shown c ++ b" doesn't build " ++ sort_text sig sort))
                    None        -> Err (Error cp (b"unknown constructor " ++ shown c))
        _                         -> Err (Error p b"expected `(as NAME SORT)`")

# `(let ((x t) …) body)`, from what follows `let`.
fn let_term src sig vars args p -> r : src~Bytes, sig~Sig, vars~List (Name, Sort), args~List (SExpr src), p~Nat,
                                       p < len src, r~Result Sorted (Error src)
    match args
        [Node binds _, body] ->
            let (bs, ss) = try bindings src sig vars binds
            if bs == []
                Err (Error p b"a `let` must bind at least one name")
            else
                let (t, s) = try term_from src sig (list.reverse (zip (list.keys bs) ss) ++ vars) body
                Ok (Let bs t, s)
        _                    -> Err (Error p b"expected `(let ((NAME TERM) …) TERM)`")

fn zip ns ss -> r : ns~List Name, ss~List Sort, r~List (Name, Sort)
    match (ns, ss)
        (n :: nr, s :: sr) -> (n, s) :: zip nr sr
        _                  -> []

fn bindings src sig vars es -> r : src~Bytes, sig~Sig, vars~List (Name, Sort), es~List (SExpr src),
                                   r~Result (List (Name, Term), List Sort) (Error src)
    match es
        []                                       -> Ok ([], [])
        Node [Leaf (Symbol n _) np, e] _ :: rest ->
            let (t, s) = try term_from src sig vars e
            let (bs, ss) = try bindings src sig vars rest
            if list.contains (list.keys bs) n then Err (Error np (twice n)) else Ok ((n, t) :: bs, s :: ss)
        e :: _                                   -> Err (Error (at e) b"expected `(NAME TERM)`")

# `(lambda ((x S)) body)`, from what follows `lambda`.
fn lambda_term src sig vars args p -> r : src~Bytes, sig~Sig, vars~List (Name, Sort), args~List (SExpr src), p~Nat,
                                          p < len src, r~Result Sorted (Error src)
    match args
        [Node [Node [Leaf (Symbol n _) _, s] _] _, body] ->
            let sort = try sort_from src sig [] s
            let (t, b) = try term_from src sig ((n, sort) :: vars) body
            Ok (Lam n sort t, Arr sort b)
        _                                                ->
            Err (Error p b"expected `(lambda ((NAME SORT)) TERM)`: a `lambda` of more than one variable is outside the subset `ckc` writes")

# A term of sort `want`, or an error at it saying what it is instead.
fn term_of src sig vars e want what -> r : src~Bytes, sig~Sig, vars~List (Name, Sort), e~SExpr src, want~Sort,
                                           what~Bytes, r~Result Term (Error src)
    let (t, s) = try term_from src sig vars e
    if s == want
        Ok t
    else
        Err (Error (at e) (what ++ b" must be of sort " ++ sort_text sig want ++ b", not " ++ sort_text sig s))

fn at e -> p : e~SExpr src, p~Nat, p < len src
    match e
        Leaf _ p -> p
        Node _ p -> p

# `((x S) …)`: variables and their sorts.
fn sorted_vars src sig es -> r : src~Bytes, sig~Sig, es~List (SExpr src), r~Result (List (Name, Sort)) (Error src)
    match es
        []                                       -> Ok []
        Node [Leaf (Symbol n _) np, s] _ :: rest ->
            let sort = try sort_from src sig [] s
            let vs = try sorted_vars src sig rest
            if list.contains (list.keys vs) n then Err (Error np (twice n)) else Ok ((n, sort) :: vs)
        e :: _                                   -> Err (Error (at e) b"expected `(NAME SORT)`")

fn twice n -> r : n~Name, r~Bytes
    shown n ++ b" is bound twice here"

# ── Commands ─────────────────────────────────────────────────────────────────

# `cmd` added to `c`, or an error at `p` saying why it can't be.
fn add_command src c cmd p -> r : src~Bytes, c~Context, cmd~Command, p~Nat, p < len src,
                                  r~Result (d~Context, list.length (term.commands c) < list.length (term.commands d)) (Error src)
    let _ = try binders_free src (term.extend (term.signature c) cmd) (term.names c) (command_binders cmd) p
    match term.add c cmd
        Ok d   ->
            have list.length_append (term.commands c) [cmd]
            Ok d
        Err pr -> Err (Error p (problem_message (term.extend (term.signature c) cmd) pr))

# ── One meaning per spelling ─────────────────────────────────────────────────
# A variable a query binds (`let`, `forall`, `lambda`, a definition's
# parameter, a datatype's parameter) never shares its spelling with a sort,
# datatype, function, constructor, tester, selector or assertion name, nor
# with a spelling Z3 gives a meaning of its own: where Z3 and this reader
# would choose different meanings for it, there is then only one. A binder
# may hide an outer binder, as in Z3.

# An error at `p` if one of `bs` is a spelling `sig`, the assertion names
# `names`, or Z3 gives a meaning.
fn binders_free src sig names bs p -> r : src~Bytes, sig~Sig, names~List Name, bs~List Name, p~Nat, p < len src,
                                          r~Result Unit (Error src)
    match bs
        []        -> Ok ()
        b :: rest ->
            if taken sig b or sort_taken sig b or list.contains names b
                Err (Error p (shown b ++ b" is bound here and has a meaning of its own outside, as a declaration, a name or a built-in: a bound variable can't share its spelling"))
            else
                binders_free src sig names rest p

# The spellings `cmd` binds.
fn command_binders cmd -> r : cmd~Command, r~List Name
    match cmd
        DeclareDatatypes ds -> dt_params ds
        DefineFuns _ ds     -> defs_binders ds
        Assume a _          -> list.keys a.vars ++ term_binders a.body ++ patterns_binders a.patterns
        Assert t _          -> term_binders t
        _                   -> []

fn dt_params ds -> r : ds~List Datatype, r~List Name
    match ds
        []        -> []
        d :: rest -> d.params ++ dt_params rest

fn defs_binders ds -> r : ds~List Def, r~List Name
    match ds
        []        -> []
        d :: rest -> list.keys d.params ++ term_binders d.body ++ defs_binders rest

fn patterns_binders ps -> r : ps~List (List Term), r~List Name
    match ps
        []        -> []
        p :: rest -> terms_binders p ++ patterns_binders rest

fn term_binders t -> r : t~Term, r~List Name
    match t
        Var _          -> []
        App _ args     -> terms_binders args
        Let binds body -> binds_binders binds ++ term_binders body
        Lam n _ body   -> n :: term_binders body

fn terms_binders ts -> r : ts~List Term, r~List Name
    match ts
        []        -> []
        t :: rest -> term_binders t ++ terms_binders rest

fn binds_binders bs -> r : bs~List (Name, Term), r~List Name
    match bs
        []             -> []
        (n, t) :: rest -> n :: term_binders t ++ binds_binders rest

# Each of `cmds` added to `c` in order.
fn add_commands src c cmds -> r : src~Bytes, c~Context, cmds~List (Command, (p~Nat, p < len src)),
                                  r~Result (d~Context, list.length (term.commands c) <= list.length (term.commands d)) (Error src)
    match cmds
        []               -> Ok c
        (cmd, p) :: rest ->
            let d = try add_command src c cmd p
            add_commands src d rest

# The last negated goal read so far: `(assert (not goal))` at `at`, and the
# assertions after it, last first. While it is held, nothing is added to
# the context, so the goal comes after all of the context's commands.
record Held src : src~Bytes
    goal~Term
    at~Nat, at < len src
    after~List (Command, (p~Nat, p < len src))

# `g` if `t` is `(not g)`.
fn negated t -> r : t~Term, r~Option Term
    match t
        App (Prim Not) [g] -> Some g
        _                  -> None

# An assertion `cmd` at `p` that isn't the goal: added to `c`, or, if a goal
# is held, held after it.
fn keep src c held cmd p -> r : src~Bytes, c~Context, held~Option (Held src), cmd~Command, p~Nat, p < len src,
                                r~Result (Context, Option (Held src)) (Error src)
    match held
        None   ->
            let d = try add_command src c cmd p
            Ok (d, None)
        Some h -> Ok (c, Some (Held h.goal h.at ((cmd, p) :: h.after)))

# `c` with the held goal and the assertions after it added as facts: they
# turned out not to be the goal.
fn flush src c held -> r : src~Bytes, c~Context, held~Option (Held src), r~Result Context (Error src)
    match held
        None   -> Ok c
        Some h ->
            let d = try add_command src c (Assert (App (Prim Not) [h.goal]) None) h.at
            add_commands src d (list.reverse h.after)

# Read a query.
export fn parse src -> r : src~Bytes, r~Result Query (Error src)
    let es = try read src
    setup src es []

# The options and the logic, then the rest.
fn setup src es acc -> r : src~Bytes, es~List (SExpr src), acc~List Opt, r~Result Query (Error src)
    match es
        Node [Leaf (Symbol c False) _, Leaf (Keyword k) kp, Leaf v _] _ :: rest if c == b"set-option" ->
            if option_ok k v
                setup src rest (Opt k v :: acc)
            else
                Err (Error kp OPTIONS)
        Node [Leaf (Symbol c False) _, Leaf (Symbol l _) lp] _ :: rest if c == b"set-logic" ->
            if l == b"ALL"
                body src rest (list.reverse acc) l term.empty None None
            else
                Err (Error lp b"only `(set-logic ALL)` is in the subset `ckc` writes")
        e :: _ ->
            Err (Error (at e) b"expected `(set-option :KEYWORD VALUE)` or `(set-logic NAME)`")
        []     ->
            Err (Error (len src) b"expected `(set-logic NAME)`")

let OPTIONS = b"only `:produce-models true`, `:produce-unsat-cores true`, and `:rlimit N` and `:timeout N` with `N` below 2^32, are options in the subset `ckc` writes"

# Whether `(set-option :k v)` is one of the options `ckc` writes.
fn option_ok k v -> r : k~Bytes, v~Atom, r~Bool
    match v
        Symbol t False -> (k == b"produce-models" or k == b"produce-unsat-cores") and t == b"true"
        # Z3 takes these as unsigned 32-bit numbers.
        Numeral n      -> (k == b"rlimit" or k == b"timeout") and n < 4294967296
        _              -> False

# The commands up to `(check-sat)`. The last `(assert (not …))` is held
# back with the assertions after it: if only assertions follow it up to
# `(check-sat)`, it is the negated goal. `broken` is where a declaration
# followed the last one held back.
fn body src es opts logic c held broken -> r : src~Bytes, es~List (SExpr src), opts~List Opt, logic~Name,
                                               c~Context, held~Option (Held src),
                                               broken~Option (p~Nat, p < len src), r~Result Query (Error src)
    match es
        []        -> Err (Error (len src) b"expected `(check-sat)`")
        e :: rest ->
            match e
                Node [Leaf (Symbol n False) _] p if n == b"check-sat" ->
                    finish src rest opts logic c held broken p
                Node [Leaf (Symbol n False) _, Node [Leaf (Symbol bang False) _, t, Leaf (Keyword k) _, Leaf (Symbol name _) np] _] _ if n == b"assert" and bang == b"!" and k == b"named" ->
                    let _ = try name_free src (term.signature c) name np
                    let cmd = try named src c t name
                    let (d, h) = try keep src c held cmd np
                    body src rest opts logic d h broken
                Node [Leaf (Symbol n False) _, Node (Leaf (Symbol f False) _ :: q) fp] p if n == b"assert" and f == b"forall" ->
                    let a = try axiom_from src (term.signature c) (plain_funs (term.defs c)) q fp
                    let (d, h) = try keep src c held (Assume a None) p
                    body src rest opts logic d h broken
                Node [Leaf (Symbol n False) _, t] p if n == b"assert" ->
                    let tm = try term_of src (term.signature c) [] t Bool b"an assertion"
                    match negated tm
                        Some g ->
                            let d = try flush src c held
                            body src rest opts logic d (Some (Held g p [])) None
                        None   ->
                            let (d, h) = try keep src c held (Assert tm None) p
                            body src rest opts logic d h broken
                Node (Leaf (Symbol n False) hp :: args) p ->
                    let d = try flush src c held
                    let cmd = try declaration src (term.signature d) n hp args p
                    let _ = try unnamed src (term.names d) (declared cmd) p
                    let d2 = try add_command src d cmd p
                    body src rest opts logic d2 None (if held == None then broken else Some p)
                _                                         ->
                    Err (Error (at e) b"expected a command")

# `(check-sat)` at `p`: the goal held back is the goal, and the assertions
# after it are facts; then `(get-unsat-core)` and `(get-value …)` may follow,
# in that order.
fn finish src rest opts logic c held broken p -> r : src~Bytes, rest~List (SExpr src), opts~List Opt, logic~Name,
                                                     c~Context, held~Option (Held src),
                                                     broken~Option (q~Nat, q < len src), p~Nat, p < len src,
                                                     r~Result Query (Error src)
    match held
        Some h ->
            let k = list.length (term.commands c)
            let d = try add_commands src c (list.reverse h.after)
            let _ = try binders_free src (term.signature d) (term.names d) (term_binders h.goal) h.at
            match term.check_fact d h.goal
                Err pr -> Err (Error h.at (b"the goal: " ++ problem_message (term.signature d) pr))
                Ok ()  ->
                    let (core, more) = unsat_core rest
                    match more
                        []     -> Ok (Query opts logic d h.goal k core None)
                        Node [Leaf (Symbol n False) _, Node [] tp] _ :: _ if n == b"get-value" ->
                            Err (Error tp b"`(get-value …)` needs at least one term")
                        Node [Leaf (Symbol n False) _, Node ts tp] _ :: after if n == b"get-value" ->
                            let (vs, _) = try terms_from src (term.signature d) [] ts
                            let _ = try binders_free src (term.signature d) (term.names d) (terms_binders vs) tp
                            match (term.check_terms d vs, after)
                                (Err pr, _) -> Err (Error tp (problem_message (term.signature d) pr))
                                (Ok (), []) -> Ok (Query opts logic d h.goal k core (Some vs))
                                (_, e :: _) -> Err (Error (at e) AFTER_CHECK_SAT)
                        e :: _ -> Err (Error (at e) AFTER_CHECK_SAT)
        None   ->
            match broken
                Some q -> Err (Error q b"only assertions may follow the negated goal, `(assert (not GOAL))`")
                None   -> Err (Error p b"no negated goal, `(assert (not GOAL))`, before `(check-sat)`")

let AFTER_CHECK_SAT = b"only `(get-unsat-core)`, then `(get-value (TERM …))`, may follow `(check-sat)`"

# Whether `es` start with `(get-unsat-core)`, and the rest after it.
fn unsat_core es -> r : es~List (SExpr src), r~(Bool, List (SExpr src))
    match es
        Node [Leaf (Symbol n False) _] _ :: rest if n == b"get-unsat-core" -> (True, rest)
        _ -> (False, es)

# A name is also a `Bool` constant, to Z3, which then reads the name where
# a term uses it. So a name and a declared function, constructor, tester or
# selector never share a spelling, whichever comes first, nor does a name
# and a word with a meaning of its own (`true`). Z3 accepts some of these;
# the subset doesn't need them. The reader checks this, not `Context`: a
# `Context` built otherwise may have a name spelled like a function.

# An error at `p` if `name` is already declared in `sig`.
fn name_free src sig name p -> r : src~Bytes, sig~Sig, name~Name, p~Nat, p < len src, r~Result Unit (Error src)
    if keyword name or reserved.is_reserved name or prim_op name 2 != None or outside name
        Err (Error p (shown name ++ b" has a meaning of its own, so it can't name an assertion"))
    else if taken sig name
        Err (Error p (shown name ++ b" is already declared, so it can't name an assertion"))
    else
        Ok ()

# The names of the functions, constructors, testers and selectors `cmd`
# declares.
fn declared cmd -> r : cmd~Command, r~List Name
    match cmd
        DeclareFun f        -> [f.name]
        DefineFuns _ ds     -> def_names ds
        DeclareDatatypes ds -> group_names ds
        _                   -> []

fn def_names ds -> r : ds~List Def, r~List Name
    match ds
        []        -> []
        d :: rest -> d.name :: def_names rest

# An error at `p` if one of `fs` is one of the names `names`.
fn unnamed src names fs p -> r : src~Bytes, names~List Name, fs~List Name, p~Nat, p < len src, r~Result Unit (Error src)
    match fs
        []        -> Ok ()
        f :: rest ->
            if list.contains names f
                Err (Error p (shown f ++ b" names an assertion before, so it can't be declared"))
            else
                unnamed src names rest p

# The numbers of the `Plain` definitions' functions.
fn plain_funs ds -> r : ds~List (Nat, Def), r~List Nat
    match ds
        []             -> []
        (n, d) :: rest ->
            match d.kind
                Plain     -> n :: plain_funs rest
                Recursive -> plain_funs rest

# The assertion `(assert (! e :named name))`: a fact, or an axiom if `e` is
# a `forall`.
fn named src c e name -> r : src~Bytes, c~Context, e~SExpr src, name~Name, r~Result Command (Error src)
    match e
        Node (Leaf (Symbol f False) _ :: q) fp if f == b"forall" ->
            let a = try axiom_from src (term.signature c) (plain_funs (term.defs c)) q fp
            Ok (Assume a (Some name))
        _ ->
            let t = try term_of src (term.signature c) [] e Bool b"an assertion"
            Ok (Assert t (Some name))

# `(forall ((x S) …) (! body :pattern (t …) …))`, or `(forall ((x S) …) body)`
# without patterns, from what follows `forall`. `plain` are the numbers of
# the functions `define-fun` defines, which no pattern may apply: Z3
# expands them where they are applied, in patterns too.
fn axiom_from src sig plain q p -> r : src~Bytes, sig~Sig, plain~List Nat, q~List (SExpr src), p~Nat, p < len src,
                                       r~Result Axiom (Error src)
    match q
        [Node [] vp, _] -> Err (Error vp b"a `forall` must bind at least one variable")
        [Node vs _, Node (Leaf (Symbol bang False) bp :: b :: attrs) _] if bang == b"!" ->
            if attrs == []
                Err (Error bp b"expected `:pattern (TERM …)` after a `forall`'s body")
            else
                let vars = try sorted_vars src sig vs
                let env = list.reverse vars
                let t = try term_of src sig env b Bool b"a `forall`'s body"
                let ps = try patterns src sig plain env attrs
                Ok (Axiom vars t ps)
        [Node vs _, b]  ->
            let vars = try sorted_vars src sig vs
            let t = try term_of src sig (list.reverse vars) b Bool b"a `forall`'s body"
            Ok (Axiom vars t [])
        _               ->
            Err (Error p b"expected `(forall ((NAME SORT) …) TERM)`, with `(! TERM :pattern (TERM …))` for patterns")

fn patterns src sig plain env attrs -> r : src~Bytes, sig~Sig, plain~List Nat, env~List (Name, Sort),
                                           attrs~List (SExpr src), r~Result (List (List Term)) (Error src)
    match attrs
        []     -> Ok []
        Leaf (Keyword k) _ :: Node [] at :: _ if k == b"pattern" ->
            Err (Error at b"a `:pattern` needs at least one term")
        Leaf (Keyword k) _ :: Node ts at :: rest if k == b"pattern" ->
            let (p, _) = try terms_from src sig env ts
            if not (list.all (pattern_term plain) p)
                Err (Error at PATTERN)
            else if not (covers (list.length env) 0 p)
                Err (Error at b"a `:pattern` must mention every variable its `forall` binds")
            else
                let ps = try patterns src sig plain env rest
                Ok (p :: ps)
        e :: _ ->
            Err (Error (at e) b"expected `:pattern (TERM …)`; other attributes are outside the subset `ckc` writes")

let PATTERN = b"a `:pattern`'s terms are in the subset `ckc` writes only as applications of `select` or of a function, constructor, tester or selector the query declares (not one `define-fun` defines: Z3 expands it), without `let` or `lambda` inside"

# Whether `t` can be a term of a pattern: an application of `select` or of
# what the query declares, other than a `define-fun` (`plain`), with no
# binder inside. Z3 rejects variables and literals there, warns about
# `not`, `and`, `or`, `=>` and `ite`, and expands a `define-fun`; it takes
# other built-ins without a word, but `ckc` writes none (measured on the
# corpus: 2,110 pattern terms apply a declared function, 229 `select`).
fn pattern_term plain t -> r : plain~List Nat, t~Term, r~Bool
    match t
        App h args ->
            let head = match h
                Fun f       -> not (list.contains plain f)
                Con _ _ _   -> True
                Is _ _      -> True
                Sel _ _ _   -> True
                Prim Select -> True
                _           -> False
            head and not (applies_any plain args) and not (binds_any args)
        _          -> False

# Whether one of `ts` has a `let` or `lambda` inside.
fn binds_any ts -> r : ts~List Term, r~Bool
    terms_binders ts != []

# Whether each variable below `n`, from `k`, occurs in one of `ts`.
fn covers n k ts -> r : n~Nat, k~Nat, k <= n, ts~List Term, r~Bool
    decreasing n - k
    if k >= n then True else occurs_any k ts and covers n (k + 1) ts

fn occurs k t -> r : k~Nat, t~Term, r~Bool
    match t
        Var i          -> i == k
        App _ args     -> occurs_any k args
        Let binds body -> occurs_binds k binds or occurs (k + list.length binds) body
        Lam _ _ body   -> occurs (k + 1) body

fn occurs_any k ts -> r : k~Nat, ts~List Term, r~Bool
    match ts
        []        -> False
        t :: rest -> occurs k t or occurs_any k rest

fn occurs_binds k bs -> r : k~Nat, bs~List (Name, Term), r~Bool
    match bs
        []             -> False
        (_, t) :: rest -> occurs k t or occurs_binds k rest

# Whether `t` applies one of the functions numbered `fs`.
fn applies fs t -> r : fs~List Nat, t~Term, r~Bool
    match t
        Var _          -> False
        App h args     ->
            let here = match h
                Fun f -> list.contains fs f
                _     -> False
            here or applies_any fs args
        Let binds body -> applies_binds fs binds or applies fs body
        Lam _ _ body   -> applies fs body

fn applies_any fs ts -> r : fs~List Nat, ts~List Term, r~Bool
    match ts
        []        -> False
        t :: rest -> applies fs t or applies_any fs rest

fn applies_binds fs bs -> r : fs~List Nat, bs~List (Name, Term), r~Bool
    match bs
        []             -> False
        (_, t) :: rest -> applies fs t or applies_binds fs rest

# A command other than an assertion: `n` is its name, at `hp`.
fn declaration src sig n hp args p -> r : src~Bytes, sig~Sig, n~Name, hp~Nat, hp < len src, args~List (SExpr src),
                                          p~Nat, p < len src, r~Result Command (Error src)
    if n == b"declare-sort"
        match args
            [Leaf (Symbol s _) sp, Leaf (Numeral k) kp] ->
                if sort_taken sig s
                    Err (Error sp (clash s b" is already a sort"))
                else if k >= 4294967296
                    Err (Error kp TOO_MANY)
                else
                    Ok (DeclareSort (SortDecl s k))
            _                                           -> Err (Error p b"expected `(declare-sort NAME NUMERAL)`")
    else if n == b"declare-fun"
        match args
            [Leaf (Symbol f _) fp, Node ps _, rs] ->
                let _ = try fresh src sig f fp
                let ss = try sorts_from src sig [] ps
                let s = try sort_from src sig [] rs
                Ok (DeclareFun (FunDecl f ss s Declared))
            _                                     -> Err (Error p b"expected `(declare-fun NAME (SORT …) SORT)`")
    else if n == b"declare-const"
        match args
            [Leaf (Symbol f _) fp, rs] ->
                let _ = try fresh src sig f fp
                let s = try sort_from src sig [] rs
                Ok (DeclareFun (FunDecl f [] s Constant))
            _                          -> Err (Error p b"expected `(declare-const NAME SORT)`")
    else if n == b"define-fun"
        match args
            [Leaf (Symbol f _) fp, Node ps _, rs, b] ->
                let _ = try fresh src sig f fp
                let d = try def_head src sig f ps rs Plain
                # Its body is read before it is declared: it can't apply itself.
                let defs = try def_bodies src sig [d] [b] p
                Ok (DefineFuns True defs)
            _                                        -> Err (Error p b"expected `(define-fun NAME ((NAME SORT) …) SORT TERM)`")
    else if n == b"define-fun-rec"
        match args
            [Leaf (Symbol f _) fp, Node ps _, rs, b] ->
                let _ = try fresh src sig f fp
                let d = try def_head src sig f ps rs Recursive
                let defs = try def_bodies src (term.extend sig (DefineFuns True [d])) [d] [b] p
                Ok (DefineFuns True defs)
            _                                        -> Err (Error p b"expected `(define-fun-rec NAME ((NAME SORT) …) SORT TERM)`")
    else if n == b"define-funs-rec"
        match args
            [Node hs _, Node bs _] ->
                let ds = try def_heads src sig hs []
                let defs = try def_bodies src (term.extend sig (DefineFuns False ds)) ds bs p
                Ok (DefineFuns False defs)
            _                      -> Err (Error p b"expected `(define-funs-rec ((NAME ((NAME SORT) …) SORT) …) (TERM …))`")
    else if n == b"declare-datatypes"
        match args
            [Node hs _, Node ds _] -> datatypes src sig hs ds p
            _                      -> Err (Error p b"expected `(declare-datatypes ((NAME NUMERAL) …) (DATATYPE …))`")
    else if outside n
        Err (Error hp (shown n ++ b" is outside the subset `ckc` writes"))
    else
        Err (Error hp (b"unknown command " ++ shown n))

# Z3 takes a sort's number of parameters as an unsigned 32-bit number.
let TOO_MANY = b"a sort can't have 2^32 or more parameters"

# An error if `f` can't name a new function.
fn fresh src sig f p -> r : src~Bytes, sig~Sig, f~Name, p~Nat, p < len src, r~Result Unit (Error src)
    if taken sig f then Err (Error p (clash f b" is already declared")) else Ok ()

# Why `n` can't be declared: it `already` is, or Z3 gives it a meaning.
fn clash n already -> r : n~Name, already~Bytes, r~Bytes
    if tester_like n
        shown n ++ b" is spelled as a tester is, `is-` and a constructor's name, so a query can't introduce it"
    else if keyword n or reserved.is_reserved n or prim_op n 2 != None or outside n
        shown n ++ b" has a meaning of its own in Z3, so a query can't declare it"
    else
        shown n ++ already

# A definition's name, parameters and result, with a placeholder body.
fn def_head src sig f ps rs kind -> r : src~Bytes, sig~Sig, f~Name, ps~List (SExpr src), rs~SExpr src, kind~DefKind,
                                        r~Result Def (Error src)
    let params = try sorted_vars src sig ps
    let s = try sort_from src sig [] rs
    Ok (Def f params s (App (Boolean True) []) False kind)

fn def_heads src sig hs acc -> r : src~Bytes, sig~Sig, hs~List (SExpr src), acc~List Def, r~Result (List Def) (Error src)
    match hs
        []                                                   -> Ok (list.reverse acc)
        Node [Leaf (Symbol f _) fp, Node ps _, rs] _ :: rest ->
            let _ = try fresh src sig f fp
            if def_named acc f
                Err (Error fp (shown f ++ b" is defined twice here"))
            else
                let d = try def_head src sig f ps rs Recursive
                def_heads src sig rest (d :: acc)
        e :: _                                               -> Err (Error (at e) b"expected `(NAME ((NAME SORT) …) SORT)`")

fn def_named ds f -> r : ds~List Def, f~Name, r~Bool
    match ds
        []        -> False
        d :: rest -> d.name == f or def_named rest f

# The definitions `ds` with the bodies `bs`, read in `sig`.
fn def_bodies src sig ds bs p -> r : src~Bytes, sig~Sig, ds~List Def, bs~List (SExpr src), p~Nat, p < len src,
                                     r~Result (List Def) (Error src)
    match (ds, bs)
        ([], [])                 -> Ok []
        (d :: drest, b :: brest) ->
            let t = try term_of src sig (list.reverse d.params) b d.result (b"the body of " ++ shown d.name)
            let rest = try def_bodies src sig drest brest p
            Ok (Def d.name d.params d.result t False d.kind :: rest)
        _                        -> Err (Error p b"as many bodies as functions are needed")

# `(declare-datatypes ((N k) …) (D …))`: the heads `hs` and declarations `ds`.
fn datatypes src sig hs ds p -> r : src~Bytes, sig~Sig, hs~List (SExpr src), ds~List (SExpr src), p~Nat, p < len src,
                                    r~Result Command (Error src)
    let shells = try dt_heads src sig hs []
    # While their constructors are read, the datatypes are known by name and
    # number of parameters only.
    let inner = term.extend sig (DeclareDatatypes shells)
    let dts = try dt_bodies src inner shells ds p
    match first_repeat (group_names dts)
        Some n -> Err (Error p (shown n ++ b" names two constructors, testers or selectors here"))
        None   ->
            match first_taken sig (introduced_names dts)
                Some n -> Err (Error p (clash n b" is already declared"))
                None   ->
                    match first_tester_taken sig (tester_names dts)
                        Some n -> Err (Error p (clash n b" is already declared"))
                        None   ->
                            if covariant (len sig.datatypes) (len sig.datatypes + list.length dts) dts
                                Ok (DeclareDatatypes dts)
                            else
                                Err (Error p NOT_COVARIANT)

let NOT_COVARIANT = b"a field whose sort is an array may not mention a datatype of its own group in its index sort, nor in its value sort unless that is itself a datatype (Z3: not co-variant)"

# The constructors' and selectors' names of a group: what it introduces.
fn introduced_names ds -> r : ds~List Datatype, r~List Name
    match ds
        []        -> []
        d :: rest -> ctor_field_names d.ctors ++ introduced_names rest

fn ctor_field_names cs -> r : cs~List Ctor, r~List Name
    match cs
        []        -> []
        c :: rest -> c.name :: field_names c.fields ++ ctor_field_names rest

# The testers of a group.
fn tester_names ds -> r : ds~List Datatype, r~List Name
    match ds
        []        -> []
        d :: rest -> list.map (\c -> tester_name c.name) d.ctors ++ tester_names rest

# The first tester already declared as something else.
fn first_tester_taken sig ns -> r : sig~Sig, ns~List Name, r~Option Name
    match ns
        []        -> None
        n :: rest ->
            if keyword n or reserved.is_reserved n or find_fun sig.funs n 0 != None or tester_of sig.datatypes n != None
                Some n
            else
                first_tester_taken sig rest

# Whether no field of `ds`, the datatypes numbered from `lo` below `hi`, is
# an array that mentions one of them in its index sort, or in its value
# sort when that isn't itself a datatype: Z3 (5.3.3) rejects such a group
# as not co-variant (measured).
fn covariant lo hi ds -> r : lo~Nat, hi~Nat, ds~List Datatype, r~Bool
    match ds
        []        -> True
        d :: rest -> list.all (\c -> list.all (\f -> field_covariant lo hi f.sort) c.fields) d.ctors and covariant lo hi rest

fn field_covariant lo hi s -> r : lo~Nat, hi~Nat, s~Sort, r~Bool
    match s
        Arr i v -> not (mentions lo hi i) and value_covariant lo hi v
        _       -> True

fn value_covariant lo hi v -> r : lo~Nat, hi~Nat, v~Sort, r~Bool
    match v
        Data _ _ -> True
        _        -> not (mentions lo hi v)

# Whether `s` mentions a datatype numbered from `lo` below `hi`.
fn mentions lo hi s -> r : lo~Nat, hi~Nat, s~Sort, r~Bool
    match s
        Seq e       -> mentions lo hi e
        Arr i v     -> mentions lo hi i or mentions lo hi v
        Data d args -> (lo <= d and d < hi) or not (list.all (\a -> not (mentions lo hi a)) args)
        Unin _ args -> not (list.all (\a -> not (mentions lo hi a)) args)
        _           -> False

fn blanks k -> r : k~Nat, r~List Name
    if k == 0 then [] else b"" :: blanks (k - 1)

fn dt_heads src sig hs acc -> r : src~Bytes, sig~Sig, hs~List (SExpr src), acc~List Datatype,
                                  r~Result (List Datatype) (Error src)
    match hs
        []                                                         -> Ok (list.reverse acc)
        Node [Leaf (Symbol n _) np, Leaf (Numeral k) kp] _ :: rest ->
            if sort_taken sig n or dt_named acc n
                Err (Error np (clash n b" is already a sort"))
            else if k >= 4294967296
                Err (Error kp TOO_MANY)
            else
                match acc
                    a :: _ if list.length a.params != k ->
                        Err (Error kp b"the datatypes of one `declare-datatypes` must all have the same number of parameters in the subset `ckc` writes")
                    _ -> dt_heads src sig rest (Datatype n (blanks k) [] :: acc)
        e :: _                                                     -> Err (Error (at e) b"expected `(NAME NUMERAL)`")

fn dt_named ds n -> r : ds~List Datatype, n~Name, r~Bool
    match ds
        []        -> False
        d :: rest -> d.name == n or dt_named rest n

fn dt_bodies src sig shells ds p -> r : src~Bytes, sig~Sig, shells~List Datatype, ds~List (SExpr src),
                                        p~Nat, p < len src, r~Result (List Datatype) (Error src)
    match (shells, ds)
        ([], [])                 -> Ok []
        (s :: srest, d :: drest) ->
            let dt = try dt_body src sig s d
            let rest = try dt_bodies src sig srest drest p
            Ok (dt :: rest)
        _                        -> Err (Error p b"as many datatypes as names are needed")

# One datatype's declaration: `(par (T …) (C …))` or `(C …)`.
fn dt_body src sig shell d -> r : src~Bytes, sig~Sig, shell~Datatype, d~SExpr src, r~Result Datatype (Error src)
    match d
        Node [Leaf (Symbol kw False) pp, Node [] _, Node _ _] _ if kw == b"par" ->
            Err (Error pp b"a datatype without parameters is written without `par` in the subset `ckc` writes")
        Node [Leaf (Symbol kw False) pp, Node ps _, Node cs _] _ if kw == b"par" ->
            let params = try param_names src ps
            if list.length params != list.length shell.params
                Err (Error pp (shown shell.name ++ b" was declared with " ++ numeral (list.length shell.params)
                               ++ b" parameters"))
            else
                let ctors = try ctors_from src sig params cs
                Ok (Datatype shell.name params ctors)
        Node cs dp ->
            if shell.params != []
                Err (Error dp (shown shell.name ++ b" was declared with parameters: expected `(par (NAME …) (…))`"))
            else
                let ctors = try ctors_from src sig [] cs
                Ok (Datatype shell.name [] ctors)
        Leaf _ dp  -> Err (Error dp b"expected a datatype's constructors")

fn param_names src ps -> r : src~Bytes, ps~List (SExpr src), r~Result (List Name) (Error src)
    match ps
        []                           -> Ok []
        Leaf (Symbol n _) np :: rest ->
            let ns = try param_names src rest
            if list.contains ns n then Err (Error np (twice n)) else Ok (n :: ns)
        e :: _                       -> Err (Error (at e) b"expected a parameter's name")

fn ctors_from src sig params cs -> r : src~Bytes, sig~Sig, params~List Name, cs~List (SExpr src),
                                       r~Result (List Ctor) (Error src)
    match cs
        []                                         -> Ok []
        Node (Leaf (Symbol c _) _ :: fs) _ :: rest ->
            let fields = try fields_from src sig params fs
            let more = try ctors_from src sig params rest
            Ok (Ctor c fields :: more)
        e :: _                                     -> Err (Error (at e) b"expected `(NAME (NAME SORT) …)`")

fn fields_from src sig params fs -> r : src~Bytes, sig~Sig, params~List Name, fs~List (SExpr src),
                                        r~Result (List Field) (Error src)
    match fs
        []                                      -> Ok []
        Node [Leaf (Symbol n _) _, s] _ :: rest ->
            let sort = try sort_from src sig params s
            let more = try fields_from src sig params rest
            Ok (Field n sort :: more)
        e :: _                                  -> Err (Error (at e) b"expected `(NAME SORT)`")

# The names a datatype group gives functions: constructors, testers,
# selectors.
fn group_names ds -> r : ds~List Datatype, r~List Name
    match ds
        []        -> []
        d :: rest -> ctor_names d.ctors ++ group_names rest

fn ctor_names cs -> r : cs~List Ctor, r~List Name
    match cs
        []        -> []
        c :: rest -> c.name :: tester_name c.name :: field_names c.fields ++ ctor_names rest

fn field_names fs -> r : fs~List Field, r~List Name
    match fs
        []        -> []
        f :: rest -> f.name :: field_names rest

fn first_repeat ns -> r : ns~List Name, r~Option Name
    match ns
        []        -> None
        n :: rest -> if list.contains rest n then Some n else first_repeat rest

fn first_taken sig ns -> r : sig~Sig, ns~List Name, r~Option Name
    match ns
        []        -> None
        n :: rest -> if taken sig n then Some n else first_taken sig rest

# ── Messages ─────────────────────────────────────────────────────────────────

fn text pieces -> r : pieces~List Bytes, r~Bytes
    bytes.concat (list.reverse pieces)

# A sort, or what it is if it isn't one of `sig`'s: only a command built
# outside `parse`, with numbers that name nothing, has such a sort.
fn sort_text sig s -> r : sig~Sig, s~Sort, r~Bytes
    if term.sort_ok sig 0 s then b"`" ++ text (w_sort sig [] s []) ++ b"`" else b"a sort that isn't declared"

fn sorts_text sig ss -> r : sig~Sig, ss~List Sort, r~Bytes
    match ss
        []        -> b""
        [s]       -> sort_text sig s
        s :: rest -> sort_text sig s ++ b", " ++ sorts_text sig rest

# Why a command can't be added, in words.
fn problem_message sig pr -> r : sig~Sig, pr~Problem, r~Bytes
    match pr
        BadSort s         -> b"the sort " ++ sort_text sig s ++ b" isn't declared, or has the wrong number of arguments"
        NoCtors d         -> b"the datatype " ++ shown d.name ++ b" has no constructors"
        BadApply h found  ->
            let what = if found == [] then b"nothing" else b"arguments of sorts " ++ sorts_text sig found
            let head = if term.head_ok sig h then b"`" ++ text (w_head sig h []) ++ b"`" else b"a function that isn't declared"
            head ++ b" can't be applied to " ++ what
        Unbound _         -> b"a variable that nothing binds"
        EmptyLet          -> b"a `let` that binds nothing"
        ConstantParams f  -> b"the constant " ++ shown f.name ++ b" has parameters"
        Expected want got -> b"expected a term of sort " ++ sort_text sig want ++ b", found one of sort " ++ sort_text sig got
        NoPattern         -> b"a `:pattern` needs at least one term"
        NotWellFounded d  -> b"the datatype " ++ shown d.name ++ b" has no values: each constructor needs a value of a sort that has none"
        NoBaseCase d      ->
            b"the datatype " ++ shown d.name
                ++ b" is not well-founded: every constructor has a field that holds a datatype of its group (also inside an array, a sequence or a declared sort) not yet shown to have a value"
        NotCovariant d    -> b"the datatype " ++ shown d.name ++ b" is in the index sort of an array in its own fields, which is not allowed"
        NamedTwice n      -> b"an assertion before this one is already named " ++ shown n
        PlainInGroup d    -> shown d.name ++ b" is defined without recursion, so it must be alone, in `define-fun`"

# ── Writing ──────────────────────────────────────────────────────────────────

# `n` in decimal digits.
export fn numeral n -> r : n~Nat, r~Bytes
    (string.display n []).bytes

# Pieces of output are collected last first, then joined (`text`).

# A symbol as SMT-LIB writes it: between bars if it must be.
export fn name_text n -> r : n~Name, r~Bytes
    text (w_name n [])

# A symbol, between bars if it isn't a simple symbol or is a reserved word.
fn w_name n acc -> r : n~Name, acc~List Bytes, r~List Bytes
    if simple n 0 and len n > 0 and not (is_digit n[0]) and not (negative n) and not (keyword n)
        n :: acc
    else
        b"|" :: n :: b"|" :: acc

# Whether `n` starts with `-` and a digit, as a negative number does.
fn negative n -> r : n~Name, r~Bool
    len n > 1 and n[0] == '-' and is_digit n[1]

fn simple n i -> r : n~Name, i~Nat, i <= len n, r~Bool
    decreasing len n - i
    if i >= len n then True else symbol_byte n[i] and simple n (i + 1)

# The name of bound variable `i`.
fn name_at ns i -> r : ns~List Name, i~Nat, i < list.length ns, r~Name
    match list.head (list.drop i ns)
        Some n -> n

# A sort; `params` name a datatype's parameters.
fn w_sort sig params s acc -> r : sig~Sig, params~List Name, s~Sort, term.sort_ok sig (list.length params) s,
                                  acc~List Bytes, r~List Bytes
    match s
        Bool        -> b"Bool" :: acc
        Int         -> b"Int" :: acc
        Seq e       -> b")" :: w_sort sig params e (b"(Seq " :: acc)
        Arr i v     -> b")" :: w_sort sig params v (b" " :: w_sort sig params i (b"(Array " :: acc))
        Data d []   -> w_name sig.datatypes[d].name acc
        Data d args -> b")" :: w_sorts sig params args (w_name sig.datatypes[d].name (b"(" :: acc))
        Unin u []   -> w_name sig.sorts[u].name acc
        Unin u args -> b")" :: w_sorts sig params args (w_name sig.sorts[u].name (b"(" :: acc))
        Param k     ->
            match list.head (list.drop k params)
                Some n -> w_name n acc

# Sorts, each after a space.
fn w_sorts sig params ss acc -> r : sig~Sig, params~List Name, ss~List Sort, term.sorts_ok sig (list.length params) ss,
                                    acc~List Bytes, r~List Bytes
    match ss
        []        -> acc
        s :: rest -> w_sorts sig params rest (w_sort sig params s (b" " :: acc))

# Sorts separated by spaces.
fn w_sort_list sig ss acc -> r : sig~Sig, ss~List Sort, term.sorts_ok sig 0 ss, acc~List Bytes, r~List Bytes
    match ss
        []        -> acc
        s :: rest -> w_sorts sig [] rest (w_sort sig [] s acc)

fn w_head sig h acc -> r : sig~Sig, h~Head, term.head_ok sig h, acc~List Bytes, r~List Bytes
    match h
        Fun f        -> w_name sig.funs[f].name acc
        Con d k args ->
            match term.ctor sig d k
                Some c -> b")" :: w_sort sig [] (Data d args) (b" " :: w_name c.name (b"(as " :: acc))
        Is d k       ->
            match term.ctor sig d k
                Some c -> w_name (tester_name c.name) acc
        Sel d k j    ->
            match term.ctor sig d k
                Some c ->
                    match list.head (list.drop j c.fields)
                        Some f -> w_name f.name acc
        Num n        -> numeral n :: acc
        Boolean b    -> (if b then b"true" else b"false") :: acc
        Prim op      -> op_text op :: acc
        ConstArr s   -> b")" :: w_sort sig [] s (b"(as const " :: acc)
        EmptySeq s   -> b")" :: w_sort sig [] s (b"(as seq.empty " :: acc)

# A term; `vars` name the bound variables, innermost first.
fn w_term sig vars t acc -> r : sig~Sig, vars~List Name, t~Term, term.heads_ok sig t,
                                term.scoped (list.length vars) t, acc~List Bytes, r~List Bytes
    match t
        Var i          -> w_name (name_at vars i) acc
        App h []       -> w_head sig h acc
        App h args     -> b")" :: w_args sig vars args (w_head sig h (b"(" :: acc))
        Let binds body ->
            let a = w_binds sig vars binds (b"(let (" :: acc)
            let inner = list.reverse (list.keys binds) ++ vars
            have list.length_keys binds
            have list.length_reverse (list.keys binds)
            have list.length_append (list.reverse (list.keys binds)) vars
            b")" :: w_term sig inner body (b") " :: a)
        Lam n s body   ->
            let a = w_sort sig [] s (b" " :: w_name n (b"(lambda ((" :: acc))
            b")" :: w_term sig (n :: vars) body (b")) " :: a)

# Terms, each after a space.
fn w_args sig vars ts acc -> r : sig~Sig, vars~List Name, ts~List Term, term.all_heads_ok sig ts,
                                 term.all_scoped (list.length vars) ts, acc~List Bytes, r~List Bytes
    match ts
        []        -> acc
        t :: rest -> w_args sig vars rest (w_term sig vars t (b" " :: acc))

# Terms separated by spaces.
fn w_term_list sig vars ts acc -> r : sig~Sig, vars~List Name, ts~List Term, term.all_heads_ok sig ts,
                                      term.all_scoped (list.length vars) ts, acc~List Bytes, r~List Bytes
    match ts
        []        -> acc
        t :: rest -> w_args sig vars rest (w_term sig vars t acc)

fn w_binds sig vars bs acc -> r : sig~Sig, vars~List Name, bs~List (Name, Term), term.binds_heads_ok sig bs,
                                  term.binds_scoped (list.length vars) bs, acc~List Bytes, r~List Bytes
    match bs
        []             -> acc
        (n, t) :: rest ->
            let b = b")" :: w_term sig vars t (b" " :: w_name n (b"(" :: acc))
            match rest
                [] -> b
                _  -> w_binds sig vars rest (b" " :: b)

# `((x S) …)`.
fn w_vars sig vs acc -> r : sig~Sig, vs~List (Name, Sort), term.sorts_ok sig 0 (term.var_sorts vs), acc~List Bytes,
                            r~List Bytes
    b")" :: w_var_list sig vs (b"(" :: acc)

fn w_var_list sig vs acc -> r : sig~Sig, vs~List (Name, Sort), term.sorts_ok sig 0 (term.var_sorts vs),
                                acc~List Bytes, r~List Bytes
    match vs
        []             -> acc
        (n, s) :: rest ->
            let a = b")" :: w_sort sig [] s (b" " :: w_name n (b"(" :: acc))
            match rest
                [] -> a
                _  -> w_var_list sig rest (b" " :: a)

fn w_atom a acc -> r : a~Atom, acc~List Bytes, r~List Bytes
    match a
        Symbol t q -> if q then b"|" :: t :: b"|" :: acc else t :: acc
        Keyword k  -> k :: b":" :: acc
        Numeral n  -> numeral n :: acc

fn w_command sig c acc -> r : sig~Sig, c~Command, term.command_ok sig c, acc~List Bytes, r~List Bytes
    match c
        DeclareSort d       -> b")\n" :: numeral d.arity :: b" " :: w_name d.name (b"(declare-sort " :: acc)
        DeclareDatatypes ds ->
            let a = b") (" :: w_dt_heads ds (b"(declare-datatypes (" :: acc)
            b"))\n" :: w_dt_bodies sig ds a
        DeclareFun f        ->
            match f.kind
                Constant -> b")\n" :: w_sort sig [] f.result (b" " :: w_name f.name (b"(declare-const " :: acc))
                _        ->
                    let a = b") " :: w_sort_list sig f.params (b" (" :: w_name f.name (b"(declare-fun " :: acc))
                    b")\n" :: w_sort sig [] f.result a
        DefineFuns True [d] ->
            let open = match d.kind
                Recursive -> b"(define-fun-rec "
                Plain     -> b"(define-fun "
            let a = b" " :: w_sort sig [] d.result (b" " :: w_vars sig d.params (b" " :: w_name d.name (open :: acc)))
            have params_env d.params
            b")\n" :: w_term sig (list.reverse (list.keys d.params)) d.body a
        DefineFuns _ ds     ->
            let a = b") (" :: w_def_heads sig ds (b"(define-funs-rec (" :: acc)
            b"))\n" :: w_def_bodies sig ds a
        Assume ax name      ->
            let env = list.reverse (list.keys ax.vars)
            have params_env ax.vars
            let head = b" " :: w_vars sig ax.vars (b"(forall " :: w_assert name acc)
            let f = match ax.patterns
                [] -> b")" :: w_term sig env ax.body head
                ps -> b"))" :: w_patterns sig env ps (w_term sig env ax.body (b"(! " :: head))
            w_named name f
        Assert t name       -> w_named name (w_term sig [] t (w_assert name acc))

# `(assert `, then `(! ` if the assertion has a name.
fn w_assert name acc -> r : name~Option Name, acc~List Bytes, r~List Bytes
    match name
        None   -> b"(assert " :: acc
        Some _ -> b"(assert (! " :: acc

# The end of an assertion: its name, if it has one, and `)`.
fn w_named name acc -> r : name~Option Name, acc~List Bytes, r~List Bytes
    match name
        None   -> b")\n" :: acc
        Some n -> b"))\n" :: w_name n (b" :named " :: acc)

# The names a binder list's body sees, one for each binder.
lemma params_env vs : vs~List (Name, Sort)
    ensures list.length (list.reverse (list.keys vs)) == list.length vs
    proof
        have list.length_keys vs
        have list.length_reverse (list.keys vs)

fn w_dt_heads ds acc -> r : ds~List Datatype, acc~List Bytes, r~List Bytes
    match ds
        []        -> acc
        d :: rest ->
            let a = b")" :: numeral (list.length d.params) :: b" " :: w_name d.name (b"(" :: acc)
            match rest
                [] -> a
                _  -> w_dt_heads rest (b" " :: a)

fn w_dt_bodies sig ds acc -> r : sig~Sig, ds~List Datatype, term.datatypes_ok sig ds, acc~List Bytes, r~List Bytes
    match ds
        []        -> acc
        d :: rest ->
            let a = match d.params
                [] -> b")" :: w_ctors sig [] d.ctors (b"(" :: acc)
                ps -> b"))" :: w_ctors sig ps d.ctors (b") (" :: w_name_list ps (b"(par (" :: acc))
            match rest
                [] -> a
                _  -> w_dt_bodies sig rest (b" " :: a)

fn w_name_list ns acc -> r : ns~List Name, acc~List Bytes, r~List Bytes
    match ns
        []        -> acc
        [n]       -> w_name n acc
        n :: rest -> w_name_list rest (b" " :: w_name n acc)

fn w_ctors sig params cs acc -> r : sig~Sig, params~List Name, cs~List Ctor, term.ctors_ok sig (list.length params) cs,
                                    acc~List Bytes, r~List Bytes
    match cs
        []        -> acc
        c :: rest ->
            let a = b")" :: w_fields sig params c.fields (w_name c.name (b"(" :: acc))
            match rest
                [] -> a
                _  -> w_ctors sig params rest (b" " :: a)

fn w_fields sig params fs acc -> r : sig~Sig, params~List Name, fs~List Field,
                                     term.sorts_ok sig (list.length params) (term.field_sorts fs), acc~List Bytes,
                                     r~List Bytes
    match fs
        []        -> acc
        f :: rest -> w_fields sig params rest (b")" :: w_sort sig params f.sort (b" " :: w_name f.name (b" (" :: acc)))

fn w_def_heads sig ds acc -> r : sig~Sig, ds~List Def, term.defs_ok sig ds, acc~List Bytes, r~List Bytes
    match ds
        []        -> acc
        d :: rest ->
            let a = b")" :: w_sort sig [] d.result (b" " :: w_vars sig d.params (b" " :: w_name d.name (b"(" :: acc)))
            match rest
                [] -> a
                _  -> w_def_heads sig rest (b" " :: a)

fn w_def_bodies sig ds acc -> r : sig~Sig, ds~List Def, term.defs_ok sig ds, acc~List Bytes, r~List Bytes
    match ds
        []        -> acc
        d :: rest ->
            have params_env d.params
            let a = w_term sig (list.reverse (list.keys d.params)) d.body acc
            match rest
                [] -> a
                _  -> w_def_bodies sig rest (b" " :: a)

fn w_patterns sig env ps acc -> r : sig~Sig, env~List Name, ps~List (List Term), term.patterns_heads_ok sig ps,
                                    term.patterns_scoped (list.length env) ps, acc~List Bytes, r~List Bytes
    match ps
        []        -> acc
        p :: rest -> w_patterns sig env rest (b")" :: w_term_list sig env p (b" :pattern (" :: acc))

# Commands, with the negated goal after the first `k` of them.
fn w_with_goal sig cs k g acc -> r : sig~Sig, cs~List Command, term.commands_ok sig cs, k~Nat, k <= list.length cs,
                                     g~Term, term.heads_ok sig g, term.scoped 0 g, acc~List Bytes, r~List Bytes
    if k == 0
        w_commands sig cs (b"))\n" :: w_term sig [] g (b"(assert (not " :: acc))
    else
        match cs
            c :: rest -> w_with_goal sig rest (k - 1) g (w_command sig c acc)

fn w_commands sig cs acc -> r : sig~Sig, cs~List Command, term.commands_ok sig cs, acc~List Bytes, r~List Bytes
    match cs
        []        -> acc
        c :: rest -> w_commands sig rest (w_command sig c acc)

fn w_options os acc -> r : os~List Opt, acc~List Bytes, r~List Bytes
    match os
        []        -> acc
        o :: rest -> w_options rest (b")\n" :: w_atom o.value (b" " :: o.key :: b"(set-option :" :: acc))

# The query as SMT-LIB text, one command per line.
export fn render q -> r : q~Query, r~Bytes
    let sig = term.signature q.context
    have term.commands_well_formed q.context
    have term.fact_heads q.context q.goal
    let start = b")\n" :: w_name q.logic (b"(set-logic " :: w_options q.options [])
    let sat = b"(check-sat)\n" :: w_with_goal sig (term.commands q.context) q.goal_at q.goal start
    let b = if q.core then b"(get-unsat-core)\n" :: sat else sat
    match q.values
        None    -> text b
        Some ts ->
            have term.terms_heads q.context ts
            text (b"))\n" :: w_term_list sig [] ts (b"(get-value (" :: b))

# ── Comparing texts ──────────────────────────────────────────────────────────

# An S-expression without positions, and with symbols without their bars:
# what `render` keeps of a query.
export enum Shape
    Word w      : w~Bytes
    Group items : items~List Shape

export fn shape e -> r : e~SExpr src, r~Shape
    match e
        Leaf (Symbol t _) _ -> Word t
        Leaf (Keyword k) _  -> Word (b":" ++ k)
        Leaf (Numeral n) _  -> Word (numeral n)
        Node items _        -> Group (list.map shape items)

export fn shapes es -> r : es~List (SExpr src), r~List Shape
    list.map shape es

# Whether `out` is how `render` writes `inp`, in a query whose declarations
# are `sig`: the same, except that a constructor of a datatype without
# parameters, written alone in `inp`, is `(as C D)` in `out`.
export fn same sig inp out -> r : sig~Sig, inp~Shape, out~Shape, r~Bool
    match (inp, out)
        (Word a, Word b)                           -> a == b
        (Word c, Group [Word a, Word c2, Word dn]) -> a == b"as" and c == c2 and bare_ctor sig c dn
        (Group xs, Group ys)                       -> same_all sig xs ys
        _                                          -> False

export fn same_all sig xs ys -> r : sig~Sig, xs~List Shape, ys~List Shape, r~Bool
    match (xs, ys)
        ([], [])           -> True
        (x :: xr, y :: yr) -> same sig x y and same_all sig xr yr
        _                  -> False

# Whether `c` is a constructor of the datatype named `dn`, which has no
# parameters.
fn bare_ctor sig c dn -> r : sig~Sig, c~Name, dn~Name, r~Bool
    match find_ctor sig.datatypes c 0
        Some (d, _) -> d < len sig.datatypes and sig.datatypes[d].name == dn and sig.datatypes[d].params == []
        None        -> False

# A shape as text.
export fn shape_text s -> r : s~Shape, r~Bytes
    text (w_shape s [])

fn w_shape s acc -> r : s~Shape, acc~List Bytes, r~List Bytes
    match s
        Word w   -> if len w > 0 and (w[0] == ':' or is_digit w[0]) then w :: acc else w_name w acc
        Group ss -> b")" :: w_shapes ss True (b"(" :: acc)

fn w_shapes ss first acc -> r : ss~List Shape, first~Bool, acc~List Bytes, r~List Bytes
    match ss
        []        -> acc
        s :: rest -> w_shapes rest False (w_shape s (if first then acc else b" " :: acc))
