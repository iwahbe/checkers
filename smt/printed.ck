# printed.ck — the terms Z3 prints in an answer, checked whole, then
# evaluated.
#
# Z3 prints values for `(get-value …)` and definitions for `(get-model)`.
# Both are read in two passes. `check` reads every term of the text, to
# its end, into a `Term`: well-formed, every name in scope, every part of
# the sort it must have; a text with anything else in it is not read,
# whether or not evaluation would reach it. Only then does `eval` compute
# values, by structural recursion on the checked terms (a call goes to a
# definition of lower rank, see `Defs`). Nothing is guessed: a name is
# the innermost binder of it, else a definition the model gives, else an
# element or a constructor, and a quoted symbol is always a name (`|1|`
# and `|true|` are names, not a numeral and a constant).

module printed

import std.list
import std.bytes
import std.char
import std.string
import std.parse (Parsable)
import smtlib
import smtlib (Atom, Symbol, Keyword, Numeral, SExpr, Leaf, Node)
import term
import term (Name, Sort, Bool, Int, Seq, Arr, Data, Unin, Param, Ctor, Datatype, Sig)
import model (Value, Truth, Integer, Sequence, Constructed, Element, ArrayElem, Domain)

# ── Checked terms ────────────────────────────────────────────────────────────

# A printed term after `check`. `Var i` is the `i`-th binder around it,
# innermost first: a definition's parameters, a `let`'s names, a
# `lambda`'s index. The sorts an array is built at are kept with it.
export enum Term
    Var i           : i~Nat
    Num n           : n~Int
    Lit b           : b~Bool
    Elem k          : k~Nat
    Con k args      : k~Nat, args~List Term
    Empty
    Unit x          : x~Term
    Concat xs       : xs~List Term
    Const s x       : s~Sort, x~Term
    Store s a i v   : s~Sort, a~Term, i~Term, v~Term
    AsArray s f     : s~Sort, f~Nat
    Lambda s body   : s~Sort, body~Term
    Call f args     : f~Nat, args~List Term
    # A `let`: its bindings in the order written, each read where the `let`
    # is; in the body the last is `Var 0`.
    Bind binds body : binds~List Term, body~Term
    Ite c a b       : c~Term, a~Term, b~Term
    Not a           : a~Term
    And xs          : xs~List Term
    Or xs           : xs~List Term
    Implies a b     : a~Term, b~Term
    Equal a b       : a~Term, b~Term
    Arith op xs     : op~Arith, xs~List Term
    Neg a           : a~Term
    Compare op a b  : op~Compare, a~Term, b~Term
    Len a           : a~Term
    # `seq.nth`; out of range, the model's `seq.nth_u` for its sort, if it
    # printed one (`u`).
    Nth a i u       : a~Term, i~Term, u~Option Nat
    Select a i      : a~Term, i~Term
    # `div` and `mod`; by zero, the model's `div0` or `mod0`, if printed.
    Div a b z       : a~Term, b~Term, z~Option Nat
    Mod a b z       : a~Term, b~Term, z~Option Nat
    # The tester and the `j`-th selector of constructor `k`.
    Is k a          : k~Nat, a~Term
    Get k j a       : k~Nat, j~Nat, a~Term
    # A function of the query's that the model doesn't define.
    Query f args    : f~Nat, args~List Term
    # A `forall` or `exists` over variables of sorts `ss`: read, not
    # evaluated.
    Quantified ss b : ss~List Sort, b~Term

export enum Arith
    Plus
    Minus
    Times

export enum Compare
    Less
    LessEq
    Greater
    GreaterEq

export fn size t -> n : t~Term, n~Nat
    match t
        Con _ args     -> 1 + sizes args
        Unit x         -> 1 + size x
        Concat xs      -> 1 + sizes xs
        Const _ x      -> 1 + size x
        Store _ a i v  -> 1 + size a + size i + size v
        Lambda _ b     -> 1 + size b
        Call _ args    -> 1 + sizes args
        Bind bs b      -> 1 + sizes bs + size b
        Ite c a b      -> 1 + size c + size a + size b
        Not a          -> 1 + size a
        And xs         -> 1 + sizes xs
        Or xs          -> 1 + sizes xs
        Implies a b    -> 1 + size a + size b
        Equal a b      -> 1 + size a + size b
        Arith _ xs     -> 1 + sizes xs
        Neg a          -> 1 + size a
        Compare _ a b  -> 1 + size a + size b
        Len a          -> 1 + size a
        Nth a i _      -> 1 + size a + size i
        Select a i     -> 1 + size a + size i
        Div a b _      -> 1 + size a + size b
        Mod a b _      -> 1 + size a + size b
        Is _ a         -> 1 + size a
        Get _ _ a      -> 1 + size a
        Query _ args   -> 1 + sizes args
        Quantified _ b -> 1 + size b
        _              -> 1

export fn sizes ts -> n : ts~List Term, n~Nat
    match ts
        []        -> 0
        t :: rest -> size t + sizes rest

# Whether binder `k` is used in `t` (`k` counts the binders around `t`).
export fn uses t k -> r : t~Term, k~Nat, r~Bool
    match t
        Var i           -> i == k
        Con _ args      -> uses_all args k
        Unit x          -> uses x k
        Concat xs       -> uses_all xs k
        Const _ x       -> uses x k
        Store _ a i v   -> uses a k or uses i k or uses v k
        Lambda _ b      -> uses b (k + 1)
        Call _ args     -> uses_all args k
        Bind bs b       -> uses_all bs k or uses b (k + list.length bs)
        Ite c a b       -> uses c k or uses a k or uses b k
        Not a           -> uses a k
        And xs          -> uses_all xs k
        Or xs           -> uses_all xs k
        Implies a b     -> uses a k or uses b k
        Equal a b       -> uses a k or uses b k
        Arith _ xs      -> uses_all xs k
        Neg a           -> uses a k
        Compare _ a b   -> uses a k or uses b k
        Len a           -> uses a k
        Nth a i _       -> uses a k or uses i k
        Select a i      -> uses a k or uses i k
        Div a b _       -> uses a k or uses b k
        Mod a b _       -> uses a k or uses b k
        Is _ a          -> uses a k
        Get _ _ a       -> uses a k
        Query _ args    -> uses_all args k
        Quantified ss b -> uses b (k + list.length ss)
        _               -> False

fn uses_all ts k -> r : ts~List Term, k~Nat, r~Bool
    match ts
        []        -> False
        t :: rest -> uses t k or uses_all rest k

# The definitions `t` calls or makes an array of.
export fn refs t -> r : t~Term, r~List Nat
    match t
        Call f args    -> f :: refs_all args
        AsArray _ f    -> [f]
        Con _ args     -> refs_all args
        Unit x         -> refs x
        Concat xs      -> refs_all xs
        Const _ x      -> refs x
        Store _ a i v  -> refs a ++ refs i ++ refs v
        Lambda _ b     -> refs b
        Bind bs b      -> refs_all bs ++ refs b
        Ite c a b      -> refs c ++ refs a ++ refs b
        Not a          -> refs a
        And xs         -> refs_all xs
        Or xs          -> refs_all xs
        Implies a b    -> refs a ++ refs b
        Equal a b      -> refs a ++ refs b
        Arith _ xs     -> refs_all xs
        Neg a          -> refs a
        Compare _ a b  -> refs a ++ refs b
        Len a          -> refs a
        Nth a i u      -> option_ref u ++ refs a ++ refs i
        Select a i     -> refs a ++ refs i
        Div a b z      -> option_ref z ++ refs a ++ refs b
        Mod a b z      -> option_ref z ++ refs a ++ refs b
        Is _ a         -> refs a
        Get _ _ a      -> refs a
        Query _ args   -> refs_all args
        Quantified _ b -> refs b
        _              -> []

fn option_ref u -> r : u~Option Nat, r~List Nat
    match u
        Some k -> [k]
        None   -> []

fn refs_all ts -> r : ts~List Term, r~List Nat
    match ts
        []        -> []
        t :: rest -> refs t ++ refs_all rest

# ── What names mean ──────────────────────────────────────────────────────────

# What a model defines that a term may call: each definition's name,
# parameters' sorts and result sort, by number.
export record Def
    name~Name
    params~List Sort
    result~Sort

# Where a term is checked: the query's declarations, the definitions the
# model gives, and the uninterpreted sorts whose elements are known (a
# universe Z3 printed: the elements are `0` to `n - 1`); an element of any
# other uninterpreted sort is read by its spelling alone.
export record Names
    sig~Sig
    defs~List Def
    universes~List (Sort, Nat)

fn bound scope n i -> r : scope~List (Name, Sort), n~Name, i~Nat, r~Option (Nat, Sort)
    match scope
        []             -> None
        (m, s) :: rest -> if m == n then Some (i, s) else bound rest n (i + 1)

# The definitions named `n` with `k` parameters, with their numbers.
fn defs_named ds n k i -> r : ds~List Def, n~Name, k~Nat, i~Nat, r~List (Nat, Def)
    match ds
        []        -> []
        d :: rest ->
            let more = defs_named rest n k (i + 1)
            if d.name == n and list.length d.params == k then (i, d) :: more else more

export fn ctor_named cs n k -> r : cs~List Ctor, n~Name, k~Nat, r~Option (Nat, Ctor)
    match cs
        []        -> None
        c :: rest -> if c.name == n then Some (k, c) else ctor_named rest n (k + 1)

# The datatype with no parameters that has a constructor named `n`.
fn ctor_sort sig n d -> r : sig~Sig, n~Name, d~Nat, d <= len sig.datatypes, r~Option Sort
    match ctor_data sig n d
        Some e -> if e < len sig.datatypes and sig.datatypes[e].params == [] then Some (Data e []) else None
        None   -> None

# The datatype that has a constructor named `n`, from the `d`-th on.
fn ctor_data sig n d -> r : sig~Sig, n~Name, d~Nat, d <= len sig.datatypes, r~Option Nat
    decreasing len sig.datatypes - d
    if d >= len sig.datatypes
        None
    else if ctor_named sig.datatypes[d].ctors n 0 != None
        Some d
    else
        ctor_data sig n (d + 1)

# The parameters' sorts that make `p` (a field sort, with `Param k` for the
# `k`-th parameter) the sort `s`, added to `acc`; `None` if none do.
fn matched p s acc -> r : p~Sort, s~Sort, acc~List (Nat, Sort), r~Option (List (Nat, Sort))
    match (p, s)
        (Param k, _)           ->
            match param_sort acc k
                Some t -> if t == s then Some acc else None
                None   -> Some ((k, s) :: acc)
        (Seq a, Seq b)         -> matched a b acc
        (Arr a b, Arr c d)     ->
            match matched a c acc
                Some more -> matched b d more
                None      -> None
        (Data d xs, Data e ys) -> if d == e then matched_all xs ys acc else None
        (Unin u xs, Unin v ys) -> if u == v then matched_all xs ys acc else None
        _                      -> if p == s then Some acc else None

fn matched_all ps ss acc -> r : ps~List Sort, ss~List Sort, acc~List (Nat, Sort), r~Option (List (Nat, Sort))
    match (ps, ss)
        ([], [])           -> Some acc
        (p :: pr, s :: sr) ->
            match matched p s acc
                Some more -> matched_all pr sr more
                None      -> None
        _                  -> None

fn param_sort acc k -> r : acc~List (Nat, Sort), k~Nat, r~Option Sort
    match acc
        []             -> None
        (j, t) :: rest -> if j == k then Some t else param_sort rest k

# The sorts of parameters `k` to `n - 1`, each one `acc` gives.
fn params_of acc k n -> r : acc~List (Nat, Sort), k~Nat, n~Nat, k <= n, r~Option (List Sort)
    decreasing n - k
    if k >= n
        Some []
    else
        match (param_sort acc k, params_of acc (k + 1) n)
            (Some t, Some ts) -> Some (t :: ts)
            _                 -> None

export fn digits_value b -> r : b~Bytes, r~Option Nat
    if len b > 0 and char.is_digit b[0]
        have string.parse_digits b
        match Parsable.parse b Int Int
            Ok (n, rest) -> if len rest == 0 then Some n else None
    else
        None

# `NAME!val!N`, Z3's name for element `N` of the sort named `NAME`, spelled
# as Z3 spells it (no leading zeros).
export fn element_number sort_name n -> r : sort_name~Name, n~Name, r~Option Nat
    let prefix = sort_name ++ b"!val!"
    if len n > len prefix and bytes.matches_at n 0 prefix
        canonical (bytes.slice n (len prefix) (len n))
    else
        None

# The number `b` spells in decimal, without leading zeros.
export fn canonical b -> r : b~Bytes, r~Option Nat
    match digits_value b
        Some k -> if len b == 1 or b[0] != '0' then Some k else None
        None   -> None

# The element `n` names in sort `s`, if `s` is an uninterpreted sort (an
# instance of it, if it has parameters) whose elements `n` can name.
fn element names s n -> r : names~Names, s~Sort, n~Name, r~Option Nat
    match s
        Unin u _ ->
            if u < len names.sig.sorts
                match element_number names.sig.sorts[u].name n
                    Some k ->
                        match universe names.universes s
                            Some count -> if k < count then Some k else None
                            None       -> Some k
                    None   -> None
            else
                None
        _        -> None

export fn universe us s -> r : us~List (Sort, Nat), s~Sort, r~Option Nat
    match us
        []             -> None
        (t, k) :: rest -> if t == s then Some k else universe rest s

# The uninterpreted sort without parameters an element named `n` is of.
fn element_sort names n u -> r : names~Names, n~Name, u~Nat, u <= len names.sig.sorts, r~Option Sort
    decreasing len names.sig.sorts - u
    if u >= len names.sig.sorts
        None
    else if element names (Unin u []) n != None
        Some (Unin u [])
    else
        element_sort names n (u + 1)

# ── Sorts ────────────────────────────────────────────────────────────────────

fn find_sort_named sig n i -> r : sig~Sig, n~Name, i~Nat, i <= len sig.sorts, r~Option Nat
    decreasing len sig.sorts - i
    if i >= len sig.sorts then None else if sig.sorts[i].name == n then Some i else find_sort_named sig n (i + 1)

fn find_data_named sig n i -> r : sig~Sig, n~Name, i~Nat, i <= len sig.datatypes, r~Option Nat
    decreasing len sig.datatypes - i
    if i >= len sig.datatypes
        None
    else if sig.datatypes[i].name == n
        Some i
    else
        find_data_named sig n (i + 1)

# The sort `e` writes, in `sig`.
export fn sort_from sig e -> r : sig~Sig, e~SExpr src, r~Result Sort Bytes
    match e
        Leaf (Symbol n q) _                  -> named sig n q []
        Node (Leaf (Symbol n q) _ :: args) _ ->
            let ss = try sorts_from sig args
            named sig n q ss
        _                                    -> Err b"a sort this reader doesn't know"

fn sorts_from sig es -> r : sig~Sig, es~List (SExpr src), r~Result (List Sort) Bytes
    match es
        []        -> Ok []
        e :: rest ->
            let s = try sort_from sig e
            let ss = try sorts_from sig rest
            Ok (s :: ss)

fn named sig n quoted args -> r : sig~Sig, n~Name, quoted~Bool, args~List Sort, r~Result Sort Bytes
    if not quoted and n == b"Int" and args == []
        Ok Int
    else if not quoted and n == b"Bool" and args == []
        Ok Bool
    else if not quoted and n == b"Seq"
        match args
            [x] -> Ok (Seq x)
            _   -> Err b"`Seq` with other than one sort"
    else if not quoted and n == b"Array"
        match args
            [i, v] -> Ok (Arr i v)
            _      -> Err b"`Array` with other than two sorts"
    else
        match find_data_named sig n 0
            Some d ->
                if d < len sig.datatypes and list.length sig.datatypes[d].params == list.length args
                    Ok (Data d args)
                else
                    Err (b"a datatype with the wrong number of arguments: " ++ n)
            None   ->
                match find_sort_named sig n 0
                    Some u ->
                        if u < len sig.sorts and sig.sorts[u].arity == list.length args
                            Ok (Unin u args)
                        else
                            Err (b"a sort with the wrong number of arguments: " ++ n)
                    None   -> Err (b"an unknown sort: " ++ n)

# ── Checking ─────────────────────────────────────────────────────────────────

# `e` checked as a term of sort `s` in `scope` (the binders around it,
# innermost first).
export fn checked names scope s e -> r : names~Names, scope~List (Name, Sort), s~Sort, e~SExpr src,
                                         r~Result Term Bytes
    match e
        Leaf (Symbol n q) _                  ->
            match bound scope n 0
                Some (i, t) -> if t == s then Ok (Var i) else Err (b"a name of another sort: " ++ n)
                None        -> symbol names s n q
        Node [Leaf (Symbol a False) _, Leaf (Symbol n q) _, t] _ if a == b"as" ->
            let written = try sort_from names.sig t
            if written != s
                Err b"an `as` whose sort isn't the one expected"
            else
                as_name names scope s n q
        Node (Node [Leaf (Symbol a False) _, Leaf (Symbol n q) _, t] _ :: args) _ if a == b"as" ->
            let written = try sort_from names.sig t
            if written != s then Err b"an `as` whose sort isn't the one expected" else as_applied names scope s n q args
        Node [Leaf (Symbol l False) _, Node [Node [Leaf (Symbol x _) _, t] _] _, body] _ if l == b"lambda" ->
            match s
                Arr i w ->
                    let written = try sort_from names.sig t
                    if written != i
                        Err b"a `lambda` whose variable isn't of the array's index sort"
                    else
                        let b = try checked names ((x, i) :: scope) w body
                        Ok (Lambda s b)
                _       -> Err b"a `lambda` where the sort isn't an array"
        Node [Leaf (Symbol u False) _, Leaf (Symbol a False) _, Leaf (Symbol f _) _] _ if u == b"_" and a == b"as-array" ->
            match s
                Arr i w ->
                    match defs_named names.defs f 1 0
                        [(k, d)] -> if d.params == [i] and d.result == w then Ok (AsArray s k) else Err (b"`as-array` of a function of other sorts: " ++ f)
                        _        -> Err (b"`as-array` of a name that isn't one function of one parameter: " ++ f)
                _       -> Err b"`as-array` where the sort isn't an array"
        Node [Leaf (Symbol l False) _, Node binds _, body] _ if l == b"let" ->
            let outside = unbind scope (bind_names binds)
            let bs = try let_sorted names scope binds (\n -> demand names outside s body n)
            let inner = list.reverse (list.map (\(n, _, t) -> (n, t)) bs) ++ scope
            let b = try checked names inner s body
            Ok (Bind (list.map (\(_, x, _) -> x) bs) b)
        Node [Leaf (Symbol m False) _, Leaf (Numeral n) _] _ if m == b"-" ->
            match s
                Int -> Ok (Num (0 - n))
                _   -> Err b"a negative numeral where the sort isn't Int"
        Node [Leaf (Symbol q False) _, Node vars _, body] _ if q == b"forall" or q == b"exists" ->
            if s != Bool
                Err (b"`" ++ q ++ b"` where the sort isn't Bool")
            else
                let vs = try quantified_vars names.sig vars
                let inner = list.reverse vs ++ scope
                match body
                    Node (Leaf (Symbol bang False) _ :: b :: attrs) _ if bang == b"!" ->
                        let x = try checked names inner Bool b
                        let _ = try patterns names inner attrs
                        Ok (Quantified (list.map (\(_, t) -> t) vs) x)
                    _ ->
                        let x = try checked names inner Bool body
                        Ok (Quantified (list.map (\(_, t) -> t) vs) x)
        Node (Leaf (Symbol k False) _ :: _) _ if binder k -> Err (binder_error k)
        Node (Leaf (Symbol n False) _ :: args) _ if builtin n -> apply names scope s n args
        Node (Leaf (Symbol n _) _ :: args) _ ->
            if args == []
                Err (b"an application with no arguments: " ++ n)
            else if bound scope n 0 != None
                Err (b"a bound name applied to arguments: " ++ n)
            else
                match defs_named names.defs n (list.length args) 0
                    []      ->
                        match head_of names.sig n
                            HCtor       -> construct names scope s n args
                            HTester d k ->
                                let x = try tester_app names scope d k n args
                                if s == Bool then Ok x else Err (b"a tester where the sort isn't Bool: " ++ n)
                            HSel d k j  ->
                                let (x, t) = try selector_app names scope d k j n args
                                if t == s then Ok x else Err (b"a selector of another sort: " ++ n)
                            HQuery f    ->
                                let (x, t) = try query_app names scope f n args
                                if t == s then Ok x else Err (b"a function of another sort: " ++ n)
                            HNone       -> Err (b"a name this reader can't read here: " ++ n)
                    several -> call names scope s n several args
        Leaf (Numeral n) _                   ->
            match s
                Int -> Ok (Num n)
                _   -> Err b"a numeral where the sort isn't Int"
        _                                    -> Err b"a term this reader doesn't know"

# `(as n s)`, with its sort `s` checked: `seq.empty`, or a constructor
# without fields (never a bound name).
fn as_name names scope s n q -> r : names~Names, scope~List (Name, Sort), s~Sort, n~Name, q~Bool, r~Result Term Bytes
    if bound scope n 0 != None
        Err (b"`as` of a bound name: " ++ n)
    else if not q and n == b"seq.empty"
        match s
            Seq _ -> Ok Empty
            _     -> Err b"seq.empty where the sort isn't a sequence"
    else
        nullary names s n

# `((as n s) args)`, with its sort `s` checked: a constant array, or a
# constructor applied to its fields.
fn as_applied names scope s n q args -> r : names~Names, scope~List (Name, Sort), s~Sort, n~Name, q~Bool,
                                            args~List (SExpr src), r~Result Term Bytes
    if bound scope n 0 != None
        Err (b"`as` of a bound name: " ++ n)
    else if not q and n == b"const"
        match (s, args)
            (Arr _ w, [x]) ->
                let v = try checked names scope w x
                Ok (Const s v)
            _              -> Err b"a constant array that isn't one value of an array sort"
    else
        construct names scope s n args

# `e` checked, with its sort, where nothing says what sort it must be.
export fn inferred names scope e -> r : names~Names, scope~List (Name, Sort), e~SExpr src, r~Result (Term, Sort) Bytes
    match e
        Leaf (Numeral n) _                   -> Ok (Num n, Int)
        Leaf (Symbol n q) _                  ->
            match bound scope n 0
                Some (i, t) -> Ok (Var i, t)
                None        ->
                    match symbol_sort names n q
                        Some t ->
                            let x = try symbol names t n q
                            Ok (x, t)
                        None   -> Err (b"a name whose sort this reader can't tell: " ++ n)
        Node [Leaf (Symbol m False) _, Leaf (Numeral n) _] _ if m == b"-" -> Ok (Num (0 - n), Int)
        Node [Leaf (Symbol a False) _, Leaf (Symbol n q) _, t] _ if a == b"as" ->
            let s = try sort_from names.sig t
            let x = try as_name names scope s n q
            Ok (x, s)
        Node (Node [Leaf (Symbol a False) _, Leaf (Symbol n q) _, t] _ :: args) _ if a == b"as" ->
            let s = try sort_from names.sig t
            let x = try as_applied names scope s n q args
            Ok (x, s)
        Node [Leaf (Symbol l False) _, Node [Node [Leaf (Symbol x _) _, t] _] _, body] _ if l == b"lambda" ->
            let i = try sort_from names.sig t
            let (b, w) = try inferred names ((x, i) :: scope) body
            Ok (Lambda (Arr i w) b, Arr i w)
        Node [Leaf (Symbol l False) _, Node binds _, body] _ if l == b"let" ->
            let bs = try let_binds names scope binds
            let inner = list.reverse (list.map (\(n, _, t) -> (n, t)) bs) ++ scope
            let (b, s) = try inferred names inner body
            Ok (Bind (list.map (\(_, x, _) -> x) bs) b, s)
        Node (Leaf (Symbol k False) _ :: _) _ if binder k -> Err (binder_error k)
        Node (Leaf (Symbol n False) _ :: args) _ if builtin n ->
            match builtin_sort names scope n args
                Some s ->
                    let x = try apply names scope s n args
                    Ok (x, s)
                None   -> Err (b"a term whose sort this reader can't tell: " ++ n)
        Node (Leaf (Symbol n _) _ :: args) _ ->
            if args == []
                Err (b"an application with no arguments: " ++ n)
            else if bound scope n 0 != None
                Err (b"a bound name applied to arguments: " ++ n)
            else
                match defs_named names.defs n (list.length args) 0
                    [(k, d)] ->
                        let xs = try checked_all names scope d.params args
                        Ok (Call k xs, d.result)
                    []       ->
                        match head_of names.sig n
                            HCtor       ->
                                match ctor_data names.sig n 0
                                    Some d ->
                                        let t = try constructed names scope d n args
                                        let x = try construct names scope t n args
                                        Ok (x, t)
                                    None   -> Err (b"not a constructor: " ++ n)
                            HTester d k ->
                                let x = try tester_app names scope d k n args
                                Ok (x, Bool)
                            HSel d k j  -> selector_app names scope d k j n args
                            HQuery f    -> query_app names scope f n args
                            HNone       -> Err (b"a name this reader can't read here: " ++ n)
                    _        -> Err (b"a call that isn't of one definition: " ++ n)
        _                                    -> Err b"a term this reader doesn't know"

# What a name applied to arguments is, when the model defines no function
# of that name: a constructor, a tester (`is-` and a constructor's name),
# a selector, or a function of the query's.
enum Head
    HCtor
    HTester d k : d~Nat, k~Nat
    HSel d k j  : d~Nat, k~Nat, j~Nat
    HQuery f    : f~Nat
    HNone

fn head_of sig n -> r : sig~Sig, n~Name, r~Head
    if ctor_data sig n 0 != None
        HCtor
    else
        match tester_in sig n 0
            Some (d, k) -> HTester d k
            None        ->
                match selector_in sig n 0
                    Some (d, k, j) -> HSel d k j
                    None           ->
                        match query_fun sig n 0
                            Some f -> HQuery f
                            None   -> HNone

fn tester_in sig n d -> r : sig~Sig, n~Name, d~Nat, d <= len sig.datatypes, r~Option (Nat, Nat)
    decreasing len sig.datatypes - d
    if d >= len sig.datatypes
        None
    else
        match tester_of sig.datatypes[d].ctors n 0
            Some k -> Some (d, k)
            None   -> tester_in sig n (d + 1)

fn tester_of cs n k -> r : cs~List Ctor, n~Name, k~Nat, r~Option Nat
    match cs
        []        -> None
        c :: rest -> if smtlib.tester_name c.name == n then Some k else tester_of rest n (k + 1)

fn selector_in sig n d -> r : sig~Sig, n~Name, d~Nat, d <= len sig.datatypes, r~Option (Nat, Nat, Nat)
    decreasing len sig.datatypes - d
    if d >= len sig.datatypes
        None
    else
        match field_of sig.datatypes[d].ctors n 0
            Some (k, j) -> Some (d, k, j)
            None        -> selector_in sig n (d + 1)

fn field_of cs n k -> r : cs~List Ctor, n~Name, k~Nat, r~Option (Nat, Nat)
    match cs
        []        -> None
        c :: rest ->
            match field_index c.fields n 0
                Some j -> Some (k, j)
                None   -> field_of rest n (k + 1)

fn field_index fs n j -> r : fs~List term.Field, n~Name, j~Nat, r~Option Nat
    match fs
        []        -> None
        f :: rest -> if f.name == n then Some j else field_index rest n (j + 1)

fn query_fun sig n i -> r : sig~Sig, n~Name, i~Nat, i <= len sig.funs, r~Option Nat
    decreasing len sig.funs - i
    if i >= len sig.funs then None else if sig.funs[i].name == n then Some i else query_fun sig n (i + 1)

# `(is-C a)`, the tester of the `k`-th constructor of the `d`-th datatype.
fn tester_app names scope d k n args -> r : names~Names, scope~List (Name, Sort), d~Nat, k~Nat, n~Name,
                                            args~List (SExpr src), r~Result Term Bytes
    match args
        [a] ->
            let (x, t) = try inferred names scope a
            match t
                Data e _ -> if e == d then Ok (Is k x) else Err (b"a tester of another datatype's value: " ++ n)
                _        -> Err (b"a tester of what isn't a datatype's value: " ++ n)
        _   -> Err (b"a tester with other than one argument: " ++ n)

# `(sel a)`, the `j`-th selector of the `k`-th constructor of the `d`-th
# datatype, with its sort.
fn selector_app names scope d k j n args -> r : names~Names, scope~List (Name, Sort), d~Nat, k~Nat, j~Nat, n~Name,
                                                args~List (SExpr src), r~Result (Term, Sort) Bytes
    match args
        [a] ->
            let (x, t) = try inferred names scope a
            match t
                Data e targs ->
                    if e == d and d < len names.sig.datatypes
                        match list.head (list.drop k names.sig.datatypes[d].ctors)
                            Some c ->
                                match list.head (list.drop j (term.field_sorts c.fields))
                                    Some f -> Ok (Get k j x, term.instantiate targs f)
                                    None   -> Err (b"a selector without its field: " ++ n)
                            None   -> Err (b"a selector without its constructor: " ++ n)
                    else
                        Err (b"a selector of another datatype's value: " ++ n)
                _            -> Err (b"a selector of what isn't a datatype's value: " ++ n)
        _   -> Err (b"a selector with other than one argument: " ++ n)

# A function of the query's, the `f`-th, applied to `args`, with its sort.
fn query_app names scope f n args -> r : names~Names, scope~List (Name, Sort), f~Nat, n~Name, args~List (SExpr src),
                                         r~Result (Term, Sort) Bytes
    if f < len names.sig.funs
        let xs = try checked_all names scope names.sig.funs[f].params args
        Ok (Query f xs, names.sig.funs[f].result)
    else
        Err (b"an undeclared function: " ++ n)

# The printed definition named `n` at parameters `ps` and result `res`.
fn printed_at names n ps res -> r : names~Names, n~Name, ps~List Sort, res~Sort, r~Option Nat
    match at_sorts (defs_named names.defs n (list.length ps) 0) ps res
        [k] -> Some k
        _   -> None

# The sort of constructor `n` of the `d`-th datatype applied to `args`:
# the datatype's parameters are the sorts that make its fields' sorts
# those of the arguments that fix them (the others are checked later, at
# the sorts found).
fn constructed names scope d n args -> r : names~Names, scope~List (Name, Sort), d~Nat, n~Name, args~List (SExpr src),
                                           r~Result Sort Bytes
    if d < len names.sig.datatypes
        let dt = names.sig.datatypes[d]
        match ctor_named dt.ctors n 0
            Some (_, c) ->
                let acc = try solved names scope (term.field_sorts c.fields) args []
                match params_of acc 0 (list.length dt.params)
                    Some ts -> Ok (Data d ts)
                    None    -> Err (b"a constructor whose sort its arguments don't tell: " ++ n)
            None        -> Err (b"not a constructor: " ++ n)
    else
        Err b"an undeclared datatype"

# The parameters' sorts fixed by `args`, added to `acc`: in order, each
# argument whose field sort (in `fs`) has a parameter not yet fixed is
# inferred, and its sort fixes them.
fn solved names scope fs args acc -> r : names~Names, scope~List (Name, Sort), fs~List Sort, args~List (SExpr src),
                                         acc~List (Nat, Sort), r~Result (List (Nat, Sort)) Bytes
    match (fs, args)
        ([], [])           -> Ok acc
        (f :: fr, a :: ar) ->
            if unsolved f acc
                let (_, t) = try inferred names scope a
                match matched f t acc
                    Some more -> solved names scope fr ar more
                    None      -> Err b"a constructor's argument of a sort its field can't have"
            else
                solved names scope fr ar acc
        _                  -> Err b"a constructor with the wrong number of arguments"

# Whether `s` has a parameter `acc` doesn't give.
fn unsolved s acc -> r : s~Sort, acc~List (Nat, Sort), r~Bool
    match s
        Param k     -> param_sort acc k == None
        Seq x       -> unsolved x acc
        Arr i v     -> unsolved i acc or unsolved v acc
        Data _ args -> unsolved_all args acc
        Unin _ args -> unsolved_all args acc
        _           -> False

fn unsolved_all ss acc -> r : ss~List Sort, acc~List (Nat, Sort), r~Bool
    match ss
        []        -> False
        s :: rest -> unsolved s acc or unsolved_all rest acc

# The sort of a symbol that isn't bound: a constant the model defines, an
# element, a constructor without fields, `true` or `false`.
fn symbol_sort names n q -> r : names~Names, n~Name, q~Bool, r~Option Sort
    if not q and (n == b"true" or n == b"false")
        Some Bool
    else
        match defs_named names.defs n 0 0
            [(_, d)] -> Some d.result
            _        ->
                match element_sort names n 0
                    Some s -> Some s
                    None   -> ctor_sort names.sig n 0

# A symbol that isn't bound, as a term of sort `s`.
fn symbol names s n q -> r : names~Names, s~Sort, n~Name, q~Bool, r~Result Term Bytes
    if not q and (n == b"true" or n == b"false")
        if s == Bool then Ok (Lit (n == b"true")) else Err b"`true` or `false` where the sort isn't Bool"
    else
        match defs_named names.defs n 0 0
            [(k, d)] -> if d.result == s then Ok (Call k []) else Err (b"a constant of another sort: " ++ n)
            []       ->
                match element names s n
                    Some k -> Ok (Elem k)
                    None   ->
                        match s
                            Data _ _ -> nullary names s n
                            _        -> Err (b"a name this reader can't read here: " ++ n)
            _        -> Err (b"a name the model defines twice: " ++ n)

# The words that bind names: only a `lambda` of one variable and a `let`
# are read.
fn binder k -> r : k~Name, r~Bool
    k == b"lambda" or k == b"let" or k == b"forall" or k == b"exists" or k == b"match" or k == b"!"

fn binder_error k -> r : k~Name, r~Bytes
    if k == b"lambda"
        b"a `lambda` that isn't of one variable, of the array's index sort"
    else if k == b"let"
        b"a `let` that isn't `(let ((NAME VALUE) …) BODY)`"
    else
        b"`" ++ k ++ b"`, which this reader doesn't read in a model"

# The names Z3 prints as operations, unquoted.
fn builtin n -> r : n~Name, r~Bool
    n == b"ite" or n == b"not" or n == b"and" or n == b"or" or n == b"=>" or n == b"=" or n == b"+" or n == b"-"
        or n == b"*" or n == b"<" or n == b"<=" or n == b">" or n == b">=" or n == b"seq.unit" or n == b"seq.++"
        or n == b"store" or n == b"seq.len" or n == b"seq.nth" or n == b"select" or n == b"div" or n == b"mod"

fn builtin_sort names scope n args -> r : names~Names, scope~List (Name, Sort), n~Name, args~List (SExpr src),
                                          r~Option Sort
    if n == b"not" or n == b"and" or n == b"or" or n == b"=>" or n == b"=" or n == b"<" or n == b"<=" or n == b">"
        or n == b">="
        Some Bool
    else if n == b"+" or n == b"-" or n == b"*" or n == b"seq.len" or n == b"div" or n == b"mod"
        Some Int
    else
        match (n, args)
            (_, [_, a, _]) if n == b"ite" -> sort_only (inferred names scope a)
            (_, [a]) if n == b"seq.unit" ->
                match inferred names scope a
                    Ok (_, t) -> Some (Seq t)
                    Err _     -> None
            (_, a :: _) if n == b"seq.++" -> sort_only (inferred names scope a)
            (_, [a, _, _]) if n == b"store" -> sort_only (inferred names scope a)
            (_, [a, _]) if n == b"seq.nth" ->
                match inferred names scope a
                    Ok (_, Seq e) -> Some e
                    _             -> None
            (_, [a, _]) if n == b"select" ->
                match inferred names scope a
                    Ok (_, Arr _ w) -> Some w
                    _               -> None
            _ -> None

fn sort_only r -> s : r~Result (Term, Sort) Bytes, s~Option Sort
    match r
        Ok (_, t) -> Some t
        Err _     -> None

# Operation `n` applied to `args`, as a term of sort `s`.
fn apply names scope s n args -> r : names~Names, scope~List (Name, Sort), s~Sort, n~Name, args~List (SExpr src),
                                     r~Result Term Bytes
    let want = \t x -> if s == t then x else Err (b"`" ++ n ++ b"` where the sort isn't the one expected")
    match args
        [c, a, b] if n == b"ite" ->
            let cv = try checked names scope Bool c
            let av = try checked names scope s a
            let bv = try checked names scope s b
            Ok (Ite cv av bv)
        [a] if n == b"not" ->
            let x = try checked names scope Bool a
            want Bool (Ok (Not x))
        _ :: _ if n == b"and" ->
            let xs = try checked_all names scope (list.map (\_ -> Bool) args) args
            want Bool (Ok (And xs))
        _ :: _ if n == b"or" ->
            let xs = try checked_all names scope (list.map (\_ -> Bool) args) args
            want Bool (Ok (Or xs))
        [a, b] if n == b"=>" ->
            let x = try checked names scope Bool a
            let y = try checked names scope Bool b
            want Bool (Ok (Implies x y))
        [a, b] if n == b"=" ->
            let (x, t) = try inferred names scope a
            let y = try checked names scope t b
            want Bool (Ok (Equal x y))
        [a] if n == b"-" ->
            let x = try checked names scope Int a
            want Int (Ok (Neg x))
        _ :: _ :: _ if n == b"+" or n == b"-" or n == b"*" ->
            let xs = try checked_all names scope (list.map (\_ -> Int) args) args
            let op = if n == b"+" then Plus else if n == b"-" then Minus else Times
            want Int (Ok (Arith op xs))
        [a, b] if n == b"<" or n == b"<=" or n == b">" or n == b">=" ->
            let x = try checked names scope Int a
            let y = try checked names scope Int b
            let op = if n == b"<" then Less else if n == b"<=" then LessEq else if n == b">" then Greater else GreaterEq
            want Bool (Ok (Compare op x y))
        [a] if n == b"seq.unit" ->
            match s
                Seq t ->
                    let x = try checked names scope t a
                    Ok (Unit x)
                _     -> Err b"seq.unit where the sort isn't a sequence"
        _ :: _ if n == b"seq.++" ->
            match s
                Seq _ ->
                    let xs = try checked_all names scope (list.map (\_ -> s) args) args
                    Ok (Concat xs)
                _     -> Err b"seq.++ where the sort isn't a sequence"
        [a, i, v] if n == b"store" ->
            match s
                Arr is vs ->
                    let x = try checked names scope s a
                    let j = try checked names scope is i
                    let w = try checked names scope vs v
                    Ok (Store s x j w)
                _         -> Err b"store where the sort isn't an array"
        [a] if n == b"seq.len" ->
            let (x, t) = try inferred names scope a
            match t
                Seq _ -> want Int (Ok (Len x))
                _     -> Err b"seq.len of what isn't a sequence"
        [a, i] if n == b"seq.nth" ->
            let x = try checked names scope (Seq s) a
            let j = try checked names scope Int i
            Ok (Nth x j (printed_at names b"seq.nth_u" [Seq s, Int] s))
        [a, i] if n == b"select" ->
            let (x, t) = try inferred names scope a
            match t
                Arr is w ->
                    let j = try checked names scope is i
                    if w == s then Ok (Select x j) else Err b"select of an array of another sort"
                _        -> Err b"select of what isn't an array"
        [a, b] if n == b"div" or n == b"mod" ->
            let x = try checked names scope Int a
            let y = try checked names scope Int b
            let z = printed_at names (if n == b"div" then b"div0" else b"mod0") [Int, Int] Int
            want Int (Ok (if n == b"div" then Div x y z else Mod x y z))
        _ -> Err (b"`" ++ n ++ b"` with the wrong number of arguments")

fn checked_all names scope ss es -> r : names~Names, scope~List (Name, Sort), ss~List Sort, es~List (SExpr src),
                                        r~Result (List Term) Bytes
    match (ss, es)
        ([], [])           -> Ok []
        (s :: sr, e :: er) ->
            let x = try checked names scope s e
            let xs = try checked_all names scope sr er
            Ok (x :: xs)
        _                  -> Err b"the wrong number of arguments"

# A `let`'s bindings, each checked in `scope` (around the `let`: SMT-LIB's
# `let` is parallel), with their names and sorts. A name bound twice in
# one `let` is an error in SMT-LIB, and not read.
fn let_binds names scope es -> r : names~Names, scope~List (Name, Sort), es~List (SExpr src),
                                   r~Result (List (Name, Term, Sort)) Bytes
    match es
        []                                      -> Ok []
        Node [Leaf (Symbol n _) _, e] _ :: rest ->
            let (x, t) = try inferred names scope e
            let more = try let_binds names scope rest
            if not (list.all (\(m, _, _) -> m != n) more) then Err (b"a `let` that binds one name twice: " ++ n) else Ok ((n, x, t) :: more)
        _                                       -> Err b"a `let` binding that isn't `(NAME VALUE)`"

# A quantifier's variables, with their sorts, distinct and at least one.
fn quantified_vars sig es -> r : sig~Sig, es~List (SExpr src), r~Result (List (Name, Sort)) Bytes
    match es
        [] -> Err b"a quantifier without variables"
        _  -> vars_of sig es

fn vars_of sig es -> r : sig~Sig, es~List (SExpr src), r~Result (List (Name, Sort)) Bytes
    match es
        []                                      -> Ok []
        Node [Leaf (Symbol n _) _, t] _ :: rest ->
            let s = try sort_from sig t
            let more = try vars_of sig rest
            if list.all (\(m, _) -> m != n) more then Ok ((n, s) :: more) else Err (b"a quantifier whose variables share a name: " ++ n)
        _                                       -> Err b"a quantifier variable that isn't `(NAME SORT)`"

# A quantifier body's attributes: each `:pattern (t …)`, every `t` a term.
fn patterns names scope es -> r : names~Names, scope~List (Name, Sort), es~List (SExpr src), r~Result Nat Bytes
    match es
        []                                      -> Ok 0
        Leaf (Keyword k) _ :: Node ts _ :: rest ->
            if k == b"pattern" and ts != []
                let _ = try inferred_all names scope ts
                patterns names scope rest
            else
                Err b"an attribute other than `:pattern (TERM …)`"
        _                                       -> Err b"an attribute other than `:pattern (TERM …)`"

# The names a `let`'s bindings bind.
fn bind_names es -> r : es~List (SExpr src), r~List Name
    match es
        []                                      -> []
        Node [Leaf (Symbol n _) _, _] _ :: rest -> n :: bind_names rest
        _ :: rest                               -> bind_names rest

# `scope` without the names `ns`.
fn unbind scope ns -> r : scope~List (Name, Sort), ns~List Name, r~List (Name, Sort)
    match scope
        []             -> []
        (n, t) :: rest -> if list.contains ns n then unbind rest ns else (n, t) :: unbind rest ns

# A `let`'s bindings, as `let_binds` reads them; a binding whose sort its
# value alone doesn't tell (a constructor with parameters only its use
# fixes) is checked at the sort `used` finds it used at in the body.
fn let_sorted names scope es used -> r : names~Names, scope~List (Name, Sort), es~List (SExpr src), used~(Name -> Option Sort),
                                         r~Result (List (Name, Term, Sort)) Bytes
    match es
        []                                      -> Ok []
        Node [Leaf (Symbol n _) _, e] _ :: rest ->
            let more = try let_sorted names scope rest used
            if not (list.all (\(m, _, _) -> m != n) more)
                Err (b"a `let` that binds one name twice: " ++ n)
            else
                match inferred names scope e
                    Ok (x, t) -> Ok ((n, x, t) :: more)
                    Err why   ->
                        match used n
                            Some t ->
                                let x = try checked names scope t e
                                Ok ((n, x, t) :: more)
                            None   -> Err why
        _                                       -> Err b"a `let` binding that isn't `(NAME VALUE)`"

# The sort the name `a` is used at in `e`, a term of sort `s`: the first
# use whose place tells its sort. `scope` holds no binder named `a`.
fn demand names scope s e a -> r : names~Names, scope~List (Name, Sort), s~Sort, e~SExpr src, a~Name, r~Option Sort
    match e
        Leaf (Symbol n _) _                  -> if n == a then Some s else None
        Node [Leaf (Symbol l False) _, Node [Node [Leaf (Symbol x _) _, t] _] _, body] _ if l == b"lambda" ->
            match (s, sort_from names.sig t)
                (Arr i w, Ok j) -> if x == a or i != j then None else demand names ((x, i) :: scope) w body a
                _               -> None
        Node [Leaf (Symbol l False) _, Node binds _, body] _ if l == b"let" ->
            if list.contains (bind_names binds) a then None else demand names (unbind scope (bind_names binds)) s body a
        Node (Leaf (Symbol k False) _ :: _) _ if binder k -> None
        Node (Leaf (Symbol n False) _ :: args) _ if builtin n -> demand_builtin names scope s n args a
        Node (Node [Leaf (Symbol q False) _, Leaf (Symbol n _) _, t] _ :: args) _ if q == b"as" ->
            match sort_from names.sig t
                Ok w  ->
                    if n == b"const"
                        match (w, args)
                            (Arr _ v, [x]) -> demand names scope v x a
                            _              -> None
                    else
                        match ctor_of names w n
                            Ok (_, fs) -> demand_all names scope fs args a
                            Err _      -> None
                Err _ -> None
        Node (Leaf (Symbol n _) _ :: args) _ ->
            if args == [] or bound scope n 0 != None
                None
            else
                match defs_named names.defs n (list.length args) 0
                    [(_, d)] -> demand_all names scope d.params args a
                    []       ->
                        match head_of names.sig n
                            HCtor    ->
                                match ctor_of names s n
                                    Ok (_, fs) -> demand_all names scope fs args a
                                    Err _      -> None
                            HQuery f -> if f < len names.sig.funs then demand_all names scope names.sig.funs[f].params args a else None
                            _        -> None
                    _        -> None
        _                                    -> None

fn demand_all names scope ss es a -> r : names~Names, scope~List (Name, Sort), ss~List Sort, es~List (SExpr src), a~Name,
                                         r~Option Sort
    match (ss, es)
        (s :: sr, e :: er) ->
            match demand names scope s e a
                Some t -> Some t
                None   -> demand_all names scope sr er a
        _                  -> None

fn demand_each names scope s es a -> r : names~Names, scope~List (Name, Sort), s~Sort, es~List (SExpr src), a~Name,
                                         r~Option Sort
    match es
        []        -> None
        e :: rest ->
            match demand names scope s e a
                Some t -> Some t
                None   -> demand_each names scope s rest a

fn demand_builtin names scope s n args a -> r : names~Names, scope~List (Name, Sort), s~Sort, n~Name, args~List (SExpr src),
                                                a~Name, r~Option Sort
    match args
        [c, x, y] if n == b"ite" -> demand_all names scope [Bool, s, s] args a
        [x, y] if n == b"=" ->
            match inferred names scope x
                Ok (_, t) -> demand_each names scope t args a
                Err _     ->
                    match inferred names scope y
                        Ok (_, t) -> demand names scope t x a
                        Err _     -> None
        [x] if n == b"seq.unit" ->
            match s
                Seq t -> demand names scope t x a
                _     -> None
        [x, i, v] if n == b"store" ->
            match s
                Arr is w -> demand_all names scope [s, is, w] args a
                _        -> None
        [x, i] if n == b"seq.nth" -> demand_all names scope [Seq s, Int] args a
        [x, i] if n == b"select" ->
            match inferred names scope x
                Ok (_, Arr is _) -> demand names scope is i a
                _                -> None
        _ ->
            if n == b"not" or n == b"and" or n == b"or" or n == b"=>"
                demand_each names scope Bool args a
            else if n == b"seq.++"
                demand_each names scope s args a
            else if n == b"seq.len"
                None
            else
                demand_each names scope Int args a

# A call of the definition named `n` at `args`, one of `ds` (those named
# `n` with as many parameters), as a term of sort `s`; a name the model
# defines at several sorts (`seq.nth_u`) is told apart by its arguments'
# sorts.
fn call names scope s n ds args -> r : names~Names, scope~List (Name, Sort), s~Sort, n~Name, ds~List (Nat, Def),
                                       args~List (SExpr src), r~Result Term Bytes
    match ds
        [(k, d)] ->
            if d.result != s
                Err (b"a function of another sort: " ++ n)
            else
                let xs = try checked_all names scope d.params args
                Ok (Call k xs)
        _        ->
            let typed = try inferred_all names scope args
            let sorts = list.map (\(_, t) -> t) typed
            match at_sorts ds sorts s
                [k] -> Ok (Call k (list.map (\(x, _) -> x) typed))
                _   -> Err (b"a call that isn't of one definition: " ++ n)

# The numbers of the definitions of `ds` with parameters of sorts `ss` and
# result sort `s`.
fn at_sorts ds ss s -> r : ds~List (Nat, Def), ss~List Sort, s~Sort, r~List Nat
    match ds
        []             -> []
        (k, d) :: rest -> if d.params == ss and d.result == s then k :: at_sorts rest ss s else at_sorts rest ss s

fn inferred_all names scope es -> r : names~Names, scope~List (Name, Sort), es~List (SExpr src),
                                      r~Result (List (Term, Sort)) Bytes
    match es
        []        -> Ok []
        e :: rest ->
            let x = try inferred names scope e
            let xs = try inferred_all names scope rest
            Ok (x :: xs)

# The constructor named `n` of datatype sort `s`, with its fields' sorts.
fn ctor_of names s n -> r : names~Names, s~Sort, n~Name, r~Result (Nat, List Sort) Bytes
    match s
        Data d targs ->
            if d < len names.sig.datatypes
                match ctor_named names.sig.datatypes[d].ctors n 0
                    Some (k, c) -> Ok (k, list.map (term.instantiate targs) (term.field_sorts c.fields))
                    None        -> Err (b"not a constructor of the sort: " ++ n)
            else
                Err b"an undeclared datatype"
        _            -> Err (b"a name this reader can't read here: " ++ n)

# Constructor `n` of datatype sort `s` applied to `args`.
fn construct names scope s n args -> r : names~Names, scope~List (Name, Sort), s~Sort, n~Name, args~List (SExpr src),
                                         r~Result Term Bytes
    let (k, fs) = try ctor_of names s n
    let xs = try checked_all names scope fs args
    Ok (Con k xs)

# Constructor `n` of datatype sort `s`, which has no fields.
fn nullary names s n -> r : names~Names, s~Sort, n~Name, r~Result Term Bytes
    let (k, fs) = try ctor_of names s n
    if fs == [] then Ok (Con k []) else Err (b"a constructor without its fields: " ++ n)

# ── Evaluating ───────────────────────────────────────────────────────────────

# What evaluation needs: the query's declarations, the elements of each
# uninterpreted sort (for normal forms of arrays), and the definitions'
# bodies with their ranks: a body calls only definitions of lower rank, so
# evaluation ends.
export record Defs
    sig~Sig
    dom~(Nat -> List Sort -> Domain)
    bodies~List (Nat, Term)

export let NO_NORMAL_FORM = b"an array with no normal form: a store at an index sort `smt.model` can't show finite and listed, or unbounded"

let INDEX_USED = b"an array whose value at an index uses the index: no normal form"

fn body_at bs f -> r : bs~List (Nat, Term), f~Nat, r~Option (Nat, Term)
    list.head (list.drop f bs)

# The value of `t`, inside a definition of rank `rank` (or above every
# definition), where `env` gives the binders' values, innermost first.
export fn eval defs rank env t -> r : defs~Defs, rank~Nat, env~List Value, t~Term, r~Result Value Bytes
    decreasing (rank, 2 * size t)
    match t
        Var i          ->
            match list.head (list.drop i env)
                Some v -> Ok v
                None   -> Err b"a binder without a value"
        Num n          -> Ok (Integer n)
        Lit b          -> Ok (Truth b)
        Elem k         -> Ok (Element k)
        Con k args     ->
            let vs = try eval_all defs rank env args
            Ok (Constructed k vs)
        Empty          -> Ok (Sequence [])
        Unit x         ->
            let v = try eval defs rank env x
            Ok (Sequence [v])
        Concat xs      ->
            let vs = try eval_all defs rank env xs
            joined vs
        Const s x      ->
            let v = try eval defs rank env x
            match model.const_array defs.sig defs.dom s v
                Some a -> Ok a
                None   -> Err NO_NORMAL_FORM
        Store s a i v  ->
            let av = try eval defs rank env a
            let iv = try eval defs rank env i
            let vv = try eval defs rank env v
            match model.store_array defs.sig defs.dom s av iv vv
                Some x -> Ok x
                None   -> Err NO_NORMAL_FORM
        AsArray s f    ->
            match body_at defs.bodies f
                Some (k, body) -> if k < rank then array_of defs k [] s body else Err b"a definition that refers to itself"
                None           -> Err b"an undefined function"
        Lambda s body  -> array_of defs rank env s body
        Call f args    ->
            let vs = try eval_all defs rank env args
            match body_at defs.bodies f
                Some (k, body) -> if k < rank then eval defs k (list.reverse vs) body else Err b"a definition that refers to itself"
                None           -> Err b"an undefined function"
        Bind bs body   ->
            let vs = try eval_all defs rank env bs
            eval defs rank (list.reverse vs ++ env) body
        Ite c a b      ->
            let cv = try eval defs rank env c
            match cv
                Truth True  -> eval defs rank env a
                Truth False -> eval defs rank env b
                _           -> Err b"not a Bool"
        Not a          ->
            let x = try eval defs rank env a
            match x
                Truth y -> Ok (Truth (not y))
                _       -> Err b"not a Bool"
        And xs         -> conj defs rank env xs
        Or xs          -> disj defs rank env xs
        Implies a b    ->
            let x = try eval defs rank env a
            let y = try eval defs rank env b
            match (x, y)
                (Truth p, Truth q) -> Ok (Truth (not p or q))
                _                  -> Err b"not a Bool"
        Equal a b      ->
            let x = try eval defs rank env a
            let y = try eval defs rank env b
            Ok (Truth (x == y))
        Arith op xs    ->
            let vs = try eval_all defs rank env xs
            arith op vs
        Neg a          ->
            let x = try eval defs rank env a
            match x
                Integer n -> Ok (Integer (0 - n))
                _         -> Err b"not an Int"
        Compare op a b ->
            let x = try eval defs rank env a
            let y = try eval defs rank env b
            match (x, y)
                (Integer p, Integer q) -> Ok (Truth (compared op p q))
                _                      -> Err b"not an Int"
        Len a          ->
            let x = try eval defs rank env a
            match x
                Sequence xs -> Ok (Integer (list.length xs))
                _           -> Err b"not a sequence"
        Nth a i u      ->
            let x = try eval defs rank env a
            let j = try eval defs rank env i
            match (x, j)
                (Sequence xs, Integer n) ->
                    if 0 <= n and n < list.length xs
                        match list.head (list.drop n xs)
                            Some v -> Ok v
                            None   -> Err b"seq.nth out of range"
                    else
                        by_printed defs rank u [x, j] b"seq.nth out of range, which the model doesn't give"
                _                        -> Err b"not a sequence and an Int"
        Select a i     ->
            let x = try eval defs rank env a
            let j = try eval defs rank env i
            match model.select_array x j
                Some v -> Ok v
                None   -> Err b"an array with no normal form"
        Div a b z      ->
            let x = try eval defs rank env a
            let y = try eval defs rank env b
            match (x, y)
                (Integer p, Integer q) -> if q != 0 then Ok (Integer (p / q)) else by_printed defs rank z [x, y] b"div by zero, which the model doesn't give"
                _                      -> Err b"not an Int"
        Mod a b z      ->
            let x = try eval defs rank env a
            let y = try eval defs rank env b
            match (x, y)
                (Integer p, Integer q) -> if q != 0 then Ok (Integer (p % q)) else by_printed defs rank z [x, y] b"mod by zero, which the model doesn't give"
                _                      -> Err b"not an Int"
        Is k a         ->
            let x = try eval defs rank env a
            match x
                Constructed l _ -> Ok (Truth (l == k))
                _               -> Err b"not a datatype's value"
        Get k j a      ->
            let x = try eval defs rank env a
            match x
                Constructed l fs ->
                    if l == k
                        match list.head (list.drop j fs)
                            Some v -> Ok v
                            None   -> Err b"a selector without its field"
                    else
                        Err b"a selector of another constructor's value, which the model doesn't give"
                _                -> Err b"not a datatype's value"
        Query _ _      -> Err b"a function of the query's, which the model doesn't define"
        Quantified _ _ -> Err b"a quantifier, which this reader doesn't evaluate"

# The printed definition `u` (of lower rank) at `vs`, or `why` if none.
fn by_printed defs rank u vs why -> r : defs~Defs, rank~Nat, u~Option Nat, vs~List Value, why~Bytes, r~Result Value Bytes
    decreasing (rank, 0)
    match u
        Some f ->
            match body_at defs.bodies f
                Some (k, body) -> if k < rank then eval defs k (list.reverse vs) body else Err b"a definition that refers to itself"
                None           -> Err b"an undefined function"
        None   -> Err why

fn eval_all defs rank env ts -> r : defs~Defs, rank~Nat, env~List Value, ts~List Term, r~Result (List Value) Bytes
    decreasing (rank, 2 * sizes ts + 1)
    match ts
        []        -> Ok []
        t :: rest ->
            let v = try eval defs rank env t
            let vs = try eval_all defs rank env rest
            Ok (v :: vs)

fn conj defs rank env ts -> r : defs~Defs, rank~Nat, env~List Value, ts~List Term, r~Result Value Bytes
    decreasing (rank, 2 * sizes ts + 1)
    match ts
        []        -> Ok (Truth True)
        t :: rest ->
            let v = try eval defs rank env t
            match v
                Truth False -> Ok (Truth False)
                Truth True  -> conj defs rank env rest
                _           -> Err b"not a Bool"

fn disj defs rank env ts -> r : defs~Defs, rank~Nat, env~List Value, ts~List Term, r~Result Value Bytes
    decreasing (rank, 2 * sizes ts + 1)
    match ts
        []        -> Ok (Truth False)
        t :: rest ->
            let v = try eval defs rank env t
            match v
                Truth True  -> Ok (Truth True)
                Truth False -> disj defs rank env rest
                _           -> Err b"not a Bool"

fn joined vs -> r : vs~List Value, r~Result Value Bytes
    match vs
        []        -> Ok (Sequence [])
        v :: rest ->
            let w = try joined rest
            match (v, w)
                (Sequence xs, Sequence ys) -> Ok (Sequence (xs ++ ys))
                _                          -> Err b"seq.++ of something that isn't a sequence"

fn arith op vs -> r : op~Arith, vs~List Value, r~Result Value Bytes
    match vs
        Integer x :: rest -> fold op x rest
        _                 -> Err b"not an Int"

fn fold op acc vs -> r : op~Arith, acc~Int, vs~List Value, r~Result Value Bytes
    match vs
        []                -> Ok (Integer acc)
        Integer y :: rest ->
            let next =
                match op
                    Plus  -> acc + y
                    Minus -> acc - y
                    Times -> acc * y
            fold op next rest
        _                 -> Err b"not an Int"

fn compared op p q -> r : op~Compare, p~Int, q~Int, r~Bool
    match op
        Less      -> p < q
        LessEq    -> p <= q
        Greater   -> p > q
        GreaterEq -> p >= q

# The array whose value at index `Var 0` is `body`, as a normal form: a
# chain of `(ite (= x c) v …)` ending in a value; `c`, `v` and that value
# may not use the index (else there is no normal form, and it isn't read).
fn array_of defs rank env s body -> r : defs~Defs, rank~Nat, env~List Value, s~Sort, body~Term, r~Result Value Bytes
    decreasing (rank, 2 * size body + 1)
    match body
        Ite (Equal (Var 0) c) v rest ->
            if uses c 0 or uses v 0
                Err INDEX_USED
            else
                let at = Truth False :: env
                let cv = try eval defs rank at c
                let vv = try eval defs rank at v
                let under = try array_of defs rank env s rest
                match model.store_array defs.sig defs.dom s under cv vv
                    Some a -> Ok a
                    None   -> Err NO_NORMAL_FORM
        Ite (Equal c (Var 0)) v rest ->
            if uses c 0 or uses v 0
                Err INDEX_USED
            else
                let at = Truth False :: env
                let cv = try eval defs rank at c
                let vv = try eval defs rank at v
                let under = try array_of defs rank env s rest
                match model.store_array defs.sig defs.dom s under cv vv
                    Some a -> Ok a
                    None   -> Err NO_NORMAL_FORM
        _                            ->
            if uses body 0
                Err INDEX_USED
            else
                let base = try eval defs rank (Truth False :: env) body
                match model.const_array defs.sig defs.dom s base
                    Some a -> Ok a
                    None   -> Err NO_NORMAL_FORM
