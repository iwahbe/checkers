# json.ck — RFC 8259 JSON: a parser and a renderer, with a proof that
# parsing what was rendered gives it back. The worked example for SPEC.md §9.
#
# Parsing has two stages, each a parser in `std.parse`'s sense: `tokenize`
# reads bytes into tokens, each with where it starts, and the instance
# `Parsable Json JsonToken` reads tokens into a value.
#
# What the compiler proves about this module (nothing here is a runtime check):
#   • every byte access `src[i]` is in bounds          (refinements on i)
#   • both stages terminate on every input             (each reader takes at least one byte or token)
#   • every Err position points inside the input       (Error's invariant, `inside`)
#   • a Json object can never hold duplicate keys      (Obj's constructor invariant)
#   • parse (render v) == Ok v for every v within the depth limit   (lemma `roundtrip`)

module std.json

import std.decimal (Decimal)          # sealed: exact decimal numbers, read and rendered
import std.utf8                       # sealed: decode_at, encode, and their lemmas
import std.array
import std.bytes                      # sealed: matches_at
import std.string
import std.char
import std.list (keys, unique, contains, reverse, join, map, max_of)   # `keys` is exported transparent
import std.parse (Parsable, Token, token, consumed, suffix, suffix_refl, suffix_trans, suffix_size, fix, fix_unfold)

# ── Data ─────────────────────────────────────────────────────────────────────

# A JSON value. An object's keys are distinct (the constructor requires
# it) and keep their order. Numbers are exact decimals.
export enum Json
    Null
    Bool b     : b~Bool
    Num n      : n~Decimal
    Str s      : s~String
    Arr items  : items~List Json
    Obj fields : fields~List (String, Json), unique (keys fields)

# Object members. Insertion order is kept; duplicates are unrepresentable.
type Members = fs~List (String, Json), unique (keys fs)

# What went wrong in a parse.
export enum ErrorKind
    UnexpectedEnd
    UnexpectedByte b : b~U8
    BadEscape
    BadUtf8
    ControlInString
    DuplicateKey k   : k~String
    TooDeep
    TrailingInput

# An error always points into the input it came from. `src` is ghost: it
# exists only in the type, so Error costs one Nat and one tag at runtime.
export record Error src : src~ghost Bytes
    pos~Nat, pos <= len src
    kind~ErrorKind

# How deeply arrays and objects may nest in what `parse` accepts.
export let MAX_DEPTH = 512

# How deeply `v`'s arrays and objects nest: 0 for a scalar.
export fn depth v -> d : v~Json, d~Nat
    match v
        Arr items  -> 1 + max_of (map depth items)
        Obj fields -> 1 + max_of (map (\(_, x) -> depth x) fields)
        _          -> 0

# ── Tokens ───────────────────────────────────────────────────────────────────

# A JSON token (RFC 8259 §2): punctuation, a string with its escapes read, a
# number, or a literal name.
export enum JsonToken
    BeginArray                # `[`
    EndArray                  # `]`
    BeginObject               # `{`
    EndObject                 # `}`
    NameSeparator             # `:`
    ValueSeparator            # `,`
    StringToken s : s~String
    NumberToken n : n~Decimal
    TrueToken
    FalseToken
    NullToken

# A token, and where its first byte is in the input.
export record Located
    at~Nat
    kind~JsonToken

instance Token JsonToken JsonToken
    fn token v t
        v

instance Token Located JsonToken
    fn token v t
        v.kind

# An input's tokens in order, and how it ends: with nothing but whitespace
# left, or with bytes that aren't a token (where they start, and where and
# why reading them failed).
export enum Tokens
    End
    Stop at pos kind : at~Nat, pos~Nat, kind~ErrorKind
    More t rest      : t~Located, rest~Tokens

instance Seq Tokens
    type Elem = Located
    fn size ts
        match ts
            More _ rest -> 1 + size rest
            _           -> 0
    fn uncons ts
        match ts
            More t rest -> Some (t, rest)
            _           -> None

# Whether `ts`'s positions are in an input of `n` bytes: each token starts
# at one of its bytes, and an error is at most at its end.
export fn inside ts n -> b : ts~Tokens, n~Nat, b~Bool
    match ts
        End           -> True
        Stop at pos _ -> at < n and pos <= n
        More t rest   -> t.at < n and inside rest n

# ── Reading tokens ───────────────────────────────────────────────────────────

# Why a token couldn't be read, and where: how many bytes were left there.
record LexError
    left~Nat
    kind~ErrorKind

# Whether a failure `r` happened within `xs`.
fn fails_within r xs -> b : r~Result a LexError, xs~Bytes, b~Bool
    match r
        Ok _  -> True
        Err e -> e.left <= len xs

# The tokens of `src`, each after any whitespace. They end with `Stop` at
# bytes that aren't a token, or at an array or object nested deeper than
# `MAX_DEPTH`.
export fn tokenize src -> r : src~Bytes, r~Tokens, inside r (len src)
    lex src (len src) 0

# The tokens of `xs`, the last `len xs` bytes of `total`, inside `depth`
# arrays and objects.
fn lex xs total depth -> r : xs~Bytes, total~Nat, len xs <= total, depth~Nat, r~Tokens, inside r total
    decreasing len xs
    let ys = skip_ws xs
    have suffix_size ys xs
    match ys
        []     -> End
        b :: _ ->
            let at = total - len ys
            if (b == '[' or b == '{') and depth >= MAX_DEPTH
                Stop at at TooDeep
            else
                match read_token ys
                    Err e        -> Stop at (total - e.left) e.kind
                    Ok (t, rest) -> More (Located at t) (lex rest total (nested depth t))

# How deeply the token after `t` is nested.
fn nested depth t -> d : depth~Nat, t~JsonToken, d~Nat
    match t
        BeginArray  -> depth + 1
        BeginObject -> depth + 1
        EndArray    -> if depth > 0 then depth - 1 else 0
        EndObject   -> if depth > 0 then depth - 1 else 0
        _           -> depth

fn is_ws b : b~U8
    b == ' ' or b == '\t' or b == '\n' or b == '\r'

# `xs` after the whitespace at its front.
fn skip_ws xs -> r : xs~Bytes, r~Bytes, suffix r xs
    let i = ws_end xs 0
    if i == 0
        have suffix_refl xs
        xs
    else
        rest_from xs i

# Where the whitespace from `i` ends.
fn ws_end xs i -> j : xs~Bytes, i~Nat, i <= len xs, j~Nat, i <= j, j <= len xs
    decreasing len xs - i
    if i < len xs and is_ws xs[i] then ws_end xs (i + 1) else i

# `xs` from byte `i` on: what is left after reading `i` bytes.
fn rest_from xs i -> r : xs~Bytes, i~Nat, i <= len xs, r~Bytes, suffix r xs, len r + i == len xs
    have drop_suffix xs i
    array.slice xs i (len xs)

# What is left after `k` bytes of `xs` is a suffix of it.
lemma drop_suffix xs k : xs~Bytes, k~Nat, k <= len xs
    ensures suffix (array.slice xs k (len xs)) xs
    proof
        let n = len xs
        if k == 0
            have array.slice_append b"" xs b""
            have suffix_refl xs
        else
            have array.uncons_slice xs
            have array.slice_join xs 1 k n
            have array.slice_append (array.slice xs 1 k) (array.slice xs k n) b""
            have drop_suffix (array.slice xs 1 n) (k - 1)

# One token from the front of `xs`.
fn read_token xs -> r : xs~Bytes, r~Result (JsonToken, Bytes) LexError, consumed r xs, fails_within r xs
    match xs
        []        -> Err (LexError 0 UnexpectedEnd)
        b :: rest ->
            if b == '['
                Ok (BeginArray, rest)
            else if b == ']'
                Ok (EndArray, rest)
            else if b == '{'
                Ok (BeginObject, rest)
            else if b == '}'
                Ok (EndObject, rest)
            else if b == ':'
                Ok (NameSeparator, rest)
            else if b == ','
                Ok (ValueSeparator, rest)
            else if b == '"'
                string_token xs
            else if b == 'n'
                name xs b"null" NullToken
            else if b == 't'
                name xs b"true" TrueToken
            else if b == 'f'
                name xs b"false" FalseToken
            else
                match Parsable.parse xs Decimal Int
                    Ok (n, after) -> Ok (NumberToken n, after)
                    Err _         -> Err (LexError (len xs) (UnexpectedByte b))

# The name `word`, read as `t`.
fn name xs word t -> r : xs~Bytes, len xs > 0, word~Bytes, len word > 0, t~JsonToken,
                         r~Result (JsonToken, Bytes) LexError, consumed r xs, fails_within r xs
    if bytes.matches_at xs 0 word           # exported postcondition: len word <= len xs
        Ok (t, rest_from xs (len word))
    else
        Err (LexError (len xs) (UnexpectedByte xs[0]))

# ── Strings ──────────────────────────────────────────────────────────────────

# A string, from its opening quote to its closing one.
fn string_token xs -> r : xs~Bytes, len xs > 0, r~Result (JsonToken, Bytes) LexError, consumed r xs,
                          fails_within r xs
    match chars xs 1 []
        Ok (s, stop) -> Ok (StringToken s, rest_from xs stop)
        Err e        -> Err e

# The characters from `k`, after those in `acc` (reversed), and where the
# string ends: just past its closing quote.
fn chars xs k acc -> r : xs~Bytes, k~Nat, 0 < k, k <= len xs, acc~List Char,
                         r~Result (String, (stop~Nat, k < stop, stop <= len xs)) LexError, fails_within r xs
    decreasing len xs - k
    if k == len xs
        Err (LexError 0 UnexpectedEnd)
    else
        let b = xs[k]
        if b == '"'
            Ok (string.from_chars (reverse acc), k + 1)
        else if b == '\\'
            match escape xs (k + 1)
                Err e         -> Err e
                Ok (c, after) -> chars xs after (c :: acc)
        else if b < 0x20
            Err (LexError (len xs - k) ControlInString)
        else
            match utf8.decode_at xs k           # k < stop: always advances
                Some (c, stop) -> chars xs stop (c :: acc)
                None           -> Err (LexError (len xs - k) BadUtf8)

# The character an escape at `i`, after `\`, stands for, and where it ends.
fn escape xs i -> r : xs~Bytes, i~Nat, i <= len xs, r~Result (Char, (stop~Nat, i < stop, stop <= len xs)) LexError,
                      fails_within r xs
    if i == len xs
        Err (LexError 0 BadEscape)
    else
        let b = xs[i]
        if b == '"'
            Ok (c'"', i + 1)
        else if b == '\\'
            Ok (c'\\', i + 1)
        else if b == '/'
            Ok (c'/', i + 1)
        else if b == 'b'
            Ok (c'\x08', i + 1)
        else if b == 'f'
            Ok (c'\x0c', i + 1)
        else if b == 'n'
            Ok (c'\n', i + 1)
        else if b == 'r'
            Ok (c'\r', i + 1)
        else if b == 't'
            Ok (c'\t', i + 1)
        else if b == 'u'
            unicode_escape xs (i + 1)
        else
            Err (LexError (len xs - i) BadEscape)

type Hex16 = n~Nat, n < 0x10000

fn hex_digit b : b~U8
    ('0' <= b and b <= '9') or ('a' <= b and b <= 'f') or ('A' <= b and b <= 'F')

# U8 is a refinement of Nat (n < 256), so `b - '0'` is Nat subtraction; its
# precondition b >= '0' follows from hex_digit b and the branch taken.
fn hex_value b -> n : b~U8, hex_digit b, n~Nat, n < 16
    if b <= '9' then b - '0' else if b <= 'F' then b - 'A' + 10 else b - 'a' + 10

# Four hex digits at `i`.
fn hex4 xs i -> r : xs~Bytes, i~Nat, i <= len xs, r~Result Hex16 LexError, fails_within r xs,
                    match r
                        Ok _  -> i + 4 <= len xs
                        Err _ -> True
    if i + 4 <= len xs and hex_digit xs[i] and hex_digit xs[i + 1]
                       and hex_digit xs[i + 2] and hex_digit xs[i + 3]
        Ok (hex_value xs[i] * 4096 + hex_value xs[i + 1] * 256
            + hex_value xs[i + 2] * 16 + hex_value xs[i + 3])         # < 0x10000: each digit < 16
    else
        Err (LexError (len xs - i) BadEscape)

# The character after `\u` at `i`: four hex digits, or a surrogate pair.
fn unicode_escape xs i -> r : xs~Bytes, i~Nat, i <= len xs, r~Result (Char, (stop~Nat, i < stop, stop <= len xs)) LexError,
                              fails_within r xs
    let hi = try hex4 xs i
    let j = i + 4
    if 0xD800 <= hi and hi < 0xDC00                 # high surrogate: needs a pair
        if bytes.matches_at xs j b"\\u"
            let lo = try hex4 xs (j + 2)
            if 0xDC00 <= lo and lo < 0xE000
                Ok (char.from_surrogates hi lo, j + 6)
            else
                Err (LexError (len xs - j) BadEscape)
        else
            Err (LexError (len xs - j) BadEscape)
    else if 0xDC00 <= hi and hi < 0xE000            # lone low surrogate
        Err (LexError (len xs - i) BadEscape)
    else
        Ok (char.from_scalar hi, j)                 # requires: not a surrogate — proven above

# ── Values from tokens ───────────────────────────────────────────────────────

# Why tokens aren't a value, and where: how many tokens were left there.
export record TokenError
    left~Nat
    kind~TokenErrorKind

# What was wrong with the tokens.
export enum TokenErrorKind
    UnexpectedToken            # the token there can't be there
    MissingValue               # they end where a value should start
    MissingKey                 # they end where an object's key should be
    MissingSeparator           # they end where `:`, `,`, `]` or `}` should be
    RepeatedKey k : k~String   # an object's key that it already has

# A value read from tokens: `Parsable.parse ts Json JsonToken`. Any depth
# of nesting is read; `parse` limits it as it reads the tokens.
instance Parsable Json JsonToken
    type Error = TokenError
    fn parse xs a t
        fix (\zs self -> value self zs zs) xs

# A value at the front of `xs`; `self` reads one from anything shorter than
# `top`.
fn value self top xs -> r : Seq s, Token (Seq.Elem s) JsonToken,
                            self~(ys~s -> sr~Result (Json, s) TokenError, Seq.size ys < Seq.size top, consumed sr ys),
                            top~ghost s, xs~s, Seq.size xs <= Seq.size top, r~Result (Json, s) TokenError,
                            consumed r xs
    match xs
        []        -> Err (TokenError 0 MissingValue)
        x :: rest ->
            match token x JsonToken
                NullToken     -> Ok (Null, rest)
                TrueToken     -> Ok (Bool True, rest)
                FalseToken    -> Ok (Bool False, rest)
                StringToken s -> Ok (Str s, rest)
                NumberToken n -> Ok (Num n, rest)
                BeginArray    ->
                    match array self top rest
                        Err e             -> Err e
                        Ok (items, after) ->
                            have suffix_trans after rest xs
                            Ok (Arr items, after)
                BeginObject   ->
                    match object self top rest
                        Err e              -> Err e
                        Ok (fields, after) ->
                            have suffix_trans after rest xs
                            Ok (Obj fields, after)          # fields~Members carries unique (keys …)
                _             -> Err (TokenError (Seq.size xs) UnexpectedToken)

# An array's items after its `[`, and its `]`.
fn array self top xs -> r : Seq s, Token (Seq.Elem s) JsonToken,
                            self~(ys~s -> sr~Result (Json, s) TokenError, Seq.size ys < Seq.size top, consumed sr ys),
                            top~ghost s, xs~s, Seq.size xs < Seq.size top, r~Result (List Json, s) TokenError,
                            consumed r xs
    match xs
        []        -> Err (TokenError 0 MissingValue)
        x :: rest ->
            match token x JsonToken
                EndArray -> Ok ([], rest)
                _        -> elements self top xs []

# Items after `acc` (reversed), each followed by `,` or, for the last, `]`.
fn elements self top xs acc -> r : Seq s, Token (Seq.Elem s) JsonToken,
                                   self~(ys~s -> sr~Result (Json, s) TokenError, Seq.size ys < Seq.size top,
                                         consumed sr ys),
                                   top~ghost s, xs~s, Seq.size xs < Seq.size top, acc~List Json,
                                   r~Result (List Json, s) TokenError, consumed r xs
    decreasing Seq.size xs
    match self xs
        Err e       -> Err e
        Ok (v, mid) ->
            match mid
                []        -> Err (TokenError 0 MissingSeparator)
                y :: rest ->
                    have suffix_refl rest
                    have suffix_trans rest mid xs
                    have suffix_size mid xs
                    match token y JsonToken
                        ValueSeparator ->
                            match elements self top rest (v :: acc)
                                Err e             -> Err e
                                Ok (items, after) ->
                                    have suffix_trans after rest xs
                                    Ok (items, after)
                        EndArray       -> Ok (reverse (v :: acc), rest)
                        _              -> Err (TokenError (Seq.size mid) UnexpectedToken)

# An object's members after its `{`, and its `}`.
fn object self top xs -> r : Seq s, Token (Seq.Elem s) JsonToken,
                             self~(ys~s -> sr~Result (Json, s) TokenError, Seq.size ys < Seq.size top, consumed sr ys),
                             top~ghost s, xs~s, Seq.size xs < Seq.size top, r~Result (Members, s) TokenError,
                             consumed r xs
    match xs
        []        -> Err (TokenError 0 MissingKey)
        x :: rest ->
            match token x JsonToken
                EndObject -> Ok ([], rest)
                _         -> members self top xs []

# Members after `acc` (reversed), each a key, `:` and a value, followed by
# `,` or, for the last, `}`.
fn members self top xs acc -> r : Seq s, Token (Seq.Elem s) JsonToken,
                                  self~(ys~s -> sr~Result (Json, s) TokenError, Seq.size ys < Seq.size top,
                                        consumed sr ys),
                                  top~ghost s, xs~s, Seq.size xs < Seq.size top, acc~Members,
                                  r~Result (Members, s) TokenError, consumed r xs
    decreasing Seq.size xs
    match xs
        []        -> Err (TokenError 0 MissingKey)
        x :: rest ->
            match token x JsonToken
                StringToken k ->
                    if contains (keys acc) k
                        Err (TokenError (Seq.size xs) (RepeatedKey k))
                    else
                        match rest
                            []         -> Err (TokenError 0 MissingSeparator)
                            c :: after ->
                                match token c JsonToken
                                    NameSeparator ->
                                        match self after
                                            Err e       -> Err e
                                            Ok (v, mid) ->
                                                have list.unique_cons k (keys acc)     # ¬contains ∧ unique ⇒ still unique
                                                let acc2 = (k, v) :: acc
                                                match mid
                                                    []        -> Err (TokenError 0 MissingSeparator)
                                                    y :: more ->
                                                        have suffix_trans mid after xs
                                                        have suffix_size mid after
                                                        have suffix_refl more
                                                        have suffix_trans more mid xs
                                                        match token y JsonToken
                                                            ValueSeparator ->
                                                                match members self top more acc2
                                                                    Err e             -> Err e
                                                                    Ok (fields, last) ->
                                                                        have suffix_trans last more xs
                                                                        Ok (fields, last)
                                                            EndObject      ->
                                                                have list.keys_reverse acc2
                                                                have list.unique_reverse (keys acc2)
                                                                Ok (reverse acc2, more)
                                                            _              ->
                                                                Err (TokenError (Seq.size mid) UnexpectedToken)
                                    _             -> Err (TokenError (Seq.size rest) UnexpectedToken)
                _             -> Err (TokenError (Seq.size xs) UnexpectedToken)

# ── Parsing ──────────────────────────────────────────────────────────────────

# Parse one JSON value (RFC 8259), with optional whitespace around it.
# An error says where in `src` it happened. Nesting deeper than
# `MAX_DEPTH` is `TooDeep`; a repeated object key is `DuplicateKey`.
export fn parse src -> r : src~Bytes, r~Result Json (Error src)
    let ts = tokenize src
    match Parsable.parse ts Json JsonToken
        Ok (v, rest) ->
            have inside_suffix rest ts (len src)
            match rest
                End         -> Ok v
                More t _    -> Err (Error t.at TrailingInput)
                Stop at _ _ -> Err (Error at TrailingInput)
        Err e        ->
            let n = Seq.size ts
            Err (located src (drop ts (if e.left <= n then n - e.left else 0) (len src)) e.kind)

# The error `e` where the tokens left are `here`. Where they end with bytes
# that aren't a token, reading those as the value, key or separator wanted
# there gives the error the bytes would.
fn located src here e -> r : src~Bytes, here~Tokens, inside here (len src), e~TokenErrorKind, r~Error src
    match here
        More t _        ->
            match e
                RepeatedKey k -> Error t.at (DuplicateKey k)
                _             -> Error t.at (UnexpectedByte src[t.at])
        Stop at pos why ->
            match e
                MissingValue -> Error pos why
                MissingKey   -> if src[at] == '"' then Error pos why else Error at (UnexpectedByte src[at])
                _            -> Error at (UnexpectedByte src[at])
        End             -> Error (len src) UnexpectedEnd

# `ts` without its first `k` tokens.
fn drop ts k n -> r : ts~Tokens, k~Nat, n~ghost Nat, inside ts n, r~Tokens, inside r n
    match ts
        More _ rest -> if k == 0 then ts else drop rest (k - 1) n
        _           -> ts

# What is left of tokens inside an input is inside it.
lemma inside_suffix rest ts n : rest~Tokens, ts~Tokens, n~Nat, suffix rest ts, inside ts n
    ensures inside rest n
    proof
        match ts
            More _ more -> if rest == ts then auto else have inside_suffix rest more n
            _           -> auto

# ── Rendering ────────────────────────────────────────────────────────────────

# `v` as compact JSON, without whitespace. `parse` gives `v` back (lemma
# `roundtrip`).
export fn render v -> s : v~Json, s~String
    match v
        Null       -> "null"
        Bool b     -> if b then "true" else "false"
        Num n      -> decimal.render n
        Str s      -> quote s
        Arr items  -> "[" ++ join "," (map render items) ++ "]"
        Obj fields -> "{" ++ join "," (map (\(k, x) -> quote k ++ ":" ++ render x) fields) ++ "}"

fn quote s -> q : s~String, q~String
    "\"" ++ string.concat_map escape_char s ++ "\""

fn escape_char c -> s : c~Char, s~String
    match c
        c'"'  -> "\\\""
        c'\\' -> "\\\\"
        c'\n' -> "\\n"
        c'\r' -> "\\r"
        c'\t' -> "\\t"
        _ if char.code c < 0x20 -> "\\u" ++ hex4_string (char.code c)
        _     -> string.from_char c

fn hex4_string n -> s : n~Nat, n < 0x10000, s~String
    string.from_chars [hex_char (n / 4096), hex_char (n / 256 % 16), hex_char (n / 16 % 16), hex_char (n % 16)]

fn hex_char d -> c : d~Nat, d < 16, c~Char
    char.from_ascii b"0123456789abcdef"[d]      # d < 16 ⇒ index in bounds

# ── Proofs ───────────────────────────────────────────────────────────────────
#
# `roundtrip` composes the stages' round trips: `lex_value`, the bytes of a
# rendered value read as `tokens_of` it, and `build`, those tokens read as
# the value.

# A byte that could continue a number (`1` then `.5` would read as `1.5`).
fn continues_number b -> r : b~U8, r~Bool
    (b >= '0' and b <= '9') or b == '.' or b == 'e' or b == 'E'

# Bytes that may legally follow a JSON value.
fn delimits post : post~Bytes
    len post == 0 or is_ws post[0] or post[0] == ',' or post[0] == ']' or post[0] == '}' or post[0] == ':'

# The first byte of a rendered value, as `read_token` dispatches on it.
fn starts_value c -> r : c~U8, r~Bool
    c == 'n' or c == 't' or c == 'f' or c == '"' or c == '[' or c == '{' or c == '-' or (c >= '0' and c <= '9')

lemma render_first v : v~Json
    let b = utf8.encode (render v)
    ensures len b > 0 and starts_value b[0]
    proof
        match v
            Num n -> have decimal.render_starts n
            _     -> auto

# How many bytes `v` renders to.
fn width v -> n : v~Json, n~Nat
    len (utf8.encode (render v))

# The tokens of `v` rendered from position `at`, then `tail`.
fn tokens_of v at tail -> r : v~Json, at~Nat, tail~Tokens, r~Tokens
    match v
        Null       -> More (Located at NullToken) tail
        Bool b     -> More (Located at (if b then TrueToken else FalseToken)) tail
        Num n      -> More (Located at (NumberToken n)) tail
        Str s      -> More (Located at (StringToken s)) tail
        Arr items  -> More (Located at BeginArray) (items_of items (at + 1) tail)
        Obj fields -> More (Located at BeginObject) (fields_of fields (at + 1) tail)

# The tokens of an array's items rendered from `at`, its `]`, then `tail`.
fn items_of items at tail -> r : items~List Json, at~Nat, tail~Tokens, r~Tokens
    match items
        []        -> More (Located at EndArray) tail
        x :: rest ->
            let e = at + width x
            match rest
                [] -> tokens_of x at (More (Located e EndArray) tail)
                _  -> tokens_of x at (More (Located e ValueSeparator) (items_of rest (e + 1) tail))

# The tokens of an object's members rendered from `at`, its `}`, then `tail`.
fn fields_of fields at tail -> r : fields~List (String, Json), at~Nat, tail~Tokens, r~Tokens
    match fields
        []             -> More (Located at EndObject) tail
        (k, x) :: rest ->
            let c = at + len (utf8.encode (quote k))
            let e = c + 1 + width x
            let after = match rest
                [] -> More (Located e EndObject) tail
                _  -> More (Located e ValueSeparator) (fields_of rest (e + 1) tail)
            More (Located at (StringToken k)) (More (Located c NameSeparator) (tokens_of x (c + 1) after))

# ── Bytes read as tokens ─────────────────────────────────────────────────────

# A rendered value is read as its tokens, at any depth it fits in, whatever
# delimits it.
lemma lex_value v post total d : v~Json, post~Bytes, delimits post, total~Nat, d~Nat, d + depth v <= MAX_DEPTH,
                                 len (utf8.encode (render v) ++ post) <= total
    let xs = utf8.encode (render v) ++ post
    ensures lex xs total d == tokens_of v (total - len xs) (lex post total d)
    proof
        have render_first v
        match v
            Null       ->
                have rest_from_append b"null" post
                have lex_step xs NullToken post total d
            Bool b     ->
                if b
                    have rest_from_append b"true" post
                    have lex_step xs TrueToken post total d
                else
                    have rest_from_append b"false" post
                    have lex_step xs FalseToken post total d
            Num n      ->
                have decimal.render_starts n
                have decimal.parse_render n post
                have render v == decimal.render n
                have read_number xs n post
                have lex_step xs (NumberToken n) post total d
            Str s      ->
                have string_token_render s post
                have lex_step xs (StringToken s) post total d
            Arr items  ->
                have max_of (map depth items) >= 0
                have d < MAX_DEPTH
                let ys = utf8.encode (join "," (map render items) ++ "]") ++ post
                have render v == "[" ++ join "," (map render items) ++ "]"
                have xs == b"[" ++ ys
                have uncons_one b"[" ys
                have lex_step xs BeginArray ys total d
                have lex_items items post total (d + 1)
            Obj fields ->
                have map_member_text fields
                have map_member_depth fields
                have render (Obj fields) == "{" ++ join "," (map member_text fields) ++ "}"
                have depth v == 1 + max_of (map member_depth fields)
                have d < MAX_DEPTH
                let ys = utf8.encode (join "," (map member_text fields) ++ "}") ++ post
                have xs == b"{" ++ ys
                have uncons_one b"{" ys
                have lex_step xs BeginObject ys total d
                have lex_fields fields post total (d + 1)

# One token read off the front of `xs`, which doesn't start with whitespace.
lemma lex_step xs t rest total d : xs~Bytes, len xs > 0, not (is_ws xs[0]), total~Nat, len xs <= total, d~Nat,
                                   not ((xs[0] == '[' or xs[0] == '{') and d >= MAX_DEPTH),
                                   t~JsonToken, rest~Bytes, read_token xs == Ok (t, rest)
    ensures lex xs total d == More (Located (total - len xs) t) (lex rest total (nested d t))
    proof
        have ws_end xs 0 == 0
        have skip_ws xs == xs
        have array.uncons_slice xs
        have Seq.uncons (skip_ws xs) == Some (xs[0], array.slice xs 1 (len xs))

# A number is read as its token.
lemma read_number xs n rest : xs~Bytes, len xs > 0, xs[0] == '-' or (xs[0] >= '0' and xs[0] <= '9'), n~Decimal,
                              rest~Bytes, Parsable.parse xs Decimal Int == Ok (n, rest)
    ensures read_token xs == Ok (NumberToken n, rest)
    proof
        have array.uncons_slice xs

# Reading one byte off `a ++ rest`, where `a` is that byte, leaves `rest`.
lemma uncons_one a rest : a~Bytes, len a == 1, rest~Bytes
    ensures Seq.uncons (a ++ rest) == Some (a[0], rest)
    proof
        have array.uncons_slice (a ++ rest)
        have array.slice_append a rest b""

# What is left after reading `pre` off `pre ++ post` is `post`.
lemma rest_from_append pre post : pre~Bytes, post~Bytes
    ensures rest_from (pre ++ post) (len pre) == post
    proof
        have array.slice_append pre post b""

# A punctuation byte is read as its token, whatever follows.
lemma lex_punct p t post total d : p~Bytes, len p == 1, t~JsonToken, post~Bytes, total~Nat, d~Nat,
                                   len (p ++ post) <= total, read_token (p ++ post) == Ok (t, post),
                                   not (is_ws p[0]), p[0] != '[', p[0] != '{'
    ensures lex (p ++ post) total d == More (Located (total - len (p ++ post)) t) (lex post total (nested d t))
    proof
        have uncons_one p post
        have lex_step (p ++ post) t post total d

# An array's items and `]`, inside an array at `d`.
lemma lex_items items post total d : items~List Json, post~Bytes, delimits post, total~Nat, d~Nat, 0 < d,
                                     d + max_of (map depth items) <= MAX_DEPTH,
                                     len (utf8.encode (join "," (map render items) ++ "]") ++ post) <= total
    let ys = utf8.encode (join "," (map render items) ++ "]") ++ post
    ensures lex ys total d == items_of items (total - len ys) (lex post total (d - 1))
    proof
        match items
            []        ->
                have uncons_one b"]" post
                have lex_punct b"]" EndArray post total d
            x :: rest ->
                have list.max_of_cons (depth x) (map depth rest)
                have d + depth x <= MAX_DEPTH
                match rest
                    [] ->
                        have join "," (map render items) == render x
                        have ys == utf8.encode (render x) ++ (b"]" ++ post)
                        have lex_value x (b"]" ++ post) total d
                        have uncons_one b"]" post
                        have lex_punct b"]" EndArray post total d
                    _  ->
                        let zs = utf8.encode (join "," (map render rest) ++ "]") ++ post
                        have join "," (map render items) == render x ++ "," ++ join "," (map render rest)
                        have ys == utf8.encode (render x) ++ (b"," ++ zs)
                        have lex_value x (b"," ++ zs) total d
                        have uncons_one b"," zs
                        have lex_punct b"," ValueSeparator zs total d
                        have lex_items rest post total d
                        have total - len (b"," ++ zs) == total - len ys + width x
                        have total - len zs == total - len ys + width x + 1
                        have nested d ValueSeparator == d

# An object's members and `}`, inside an object at `d`.
lemma lex_fields fields post total d : fields~List (String, Json), post~Bytes, delimits post, total~Nat, d~Nat, 0 < d,
                                       d + max_of (map member_depth fields) <= MAX_DEPTH,
                                       len (utf8.encode (join "," (map member_text fields) ++ "}") ++ post) <= total
    let ys = utf8.encode (join "," (map member_text fields) ++ "}") ++ post
    ensures lex ys total d == fields_of fields (total - len ys) (lex post total (d - 1))
    proof
        match fields
            []             ->
                have uncons_one b"}" post
                have lex_punct b"}" EndObject post total d
            (k, x) :: rest ->
                have list.max_of_cons (depth x) (map member_depth rest)
                have member_text (k, x) == quote k ++ ":" ++ render x
                have member_depth (k, x) == depth x
                let tail = match rest
                    [] -> "}"
                    _  -> "," ++ join "," (map member_text rest) ++ "}"
                have join "," (map member_text fields) ++ "}" == quote k ++ ":" ++ render x ++ tail
                let after = utf8.encode tail ++ post
                have ys == utf8.encode (quote k) ++ (b":" ++ (utf8.encode (render x) ++ after))
                have lex_member k x after total d
                let e = total - len after
                match rest
                    [] ->
                        have after == b"}" ++ post
                        have uncons_one b"}" post
                        have lex_punct b"}" EndObject post total d
                        have nested d EndObject == d - 1
                        have lex after total d == More (Located e EndObject) (lex post total (d - 1))
                    _  ->
                        let zs = utf8.encode (join "," (map member_text rest) ++ "}") ++ post
                        have after == b"," ++ zs
                        have uncons_one b"," zs
                        have lex_punct b"," ValueSeparator zs total d
                        have nested d ValueSeparator == d
                        have lex after total d == More (Located e ValueSeparator) (lex zs total d)
                        have lex_fields rest post total d
                        have total - len zs == e + 1

# One member, `"k":x`, before what follows it.
lemma lex_member k x after total d : k~String, x~Json, after~Bytes, delimits after, total~Nat, d~Nat,
                                     d + depth x <= MAX_DEPTH,
                                     len (utf8.encode (quote k) ++ (b":" ++ (utf8.encode (render x) ++ after))) <= total
    let ws = utf8.encode (render x) ++ after
    let ys = utf8.encode (quote k) ++ (b":" ++ ws)
    let at = total - len ys
    let c = at + len (utf8.encode (quote k))
    ensures lex ys total d == More (Located at (StringToken k)) (More (Located c NameSeparator) (tokens_of x (c + 1) (lex after total d)))
        and total - len after == c + 1 + width x
    proof
        have quote_first k
        have string_token_render k (b":" ++ ws)
        have lex_step ys (StringToken k) (b":" ++ ws) total d
        have uncons_one b":" ws
        have lex_punct b":" NameSeparator ws total d
        have lex_value x after total d

# ── Strings read back ────────────────────────────────────────────────────────

# The escaped text of characters, one after another: what `quote` writes
# between its quotes (string.concat_map_chars).
fn escaped cs -> s : cs~List Char, s~String
    list.join "" (map escape_char cs)

# A hex digit's character reads back as that digit.
lemma hex_char_round d : d~Nat, d < 16
    let b = char.code (hex_char d)
    ensures b < 128 and hex_digit b and hex_value b == d
    proof
        auto

# The bytes `hex4_string` writes: one ASCII hex digit per four bits, high first.
lemma hex4_bytes n : n~Nat, n < 0x10000
    let b = utf8.encode (hex4_string n)
    ensures len b == 4
        and b[0] == char.code (hex_char (n / 4096)) and b[1] == char.code (hex_char (n / 256 % 16))
        and b[2] == char.code (hex_char (n / 16 % 16)) and b[3] == char.code (hex_char (n % 16))
    proof
        let d0 = hex_char (n / 4096)
        let d1 = hex_char (n / 256 % 16)
        let d2 = hex_char (n / 16 % 16)
        let d3 = hex_char (n % 16)
        have hex_char_round (n / 4096)
        have hex_char_round (n / 256 % 16)
        have hex_char_round (n / 16 % 16)
        have hex_char_round (n % 16)
        have string.from_char_bytes d0
        have string.from_char_bytes d1
        have string.from_char_bytes d2
        have string.from_char_bytes d3
        have string.from_chars_cons d0 [d1, d2, d3]
        have string.from_chars_cons d1 [d2, d3]
        have string.from_chars_cons d2 [d3]
        have string.from_chars_cons d3 []
        have string.from_chars_nil

# `hex4` reads back what `hex4_string` writes.
lemma hex4_round n pre post : n~Nat, n < 0x10000, pre~Bytes, post~Bytes
    let xs = pre ++ utf8.encode (hex4_string n) ++ post
    ensures len (utf8.encode (hex4_string n)) == 4 and hex4 xs (len pre) == Ok n
    proof
        have hex4_bytes n
        have hex_char_round (n / 4096)
        have hex_char_round (n / 256 % 16)
        have hex_char_round (n / 16 % 16)
        have hex_char_round (n % 16)

# One character, escaped, is read back as itself, whatever follows.
lemma char_step c pre post acc : c~Char, pre~Bytes, len pre > 0, post~Bytes, acc~List Char
    let xs = pre ++ utf8.encode (escape_char c) ++ post
    ensures chars xs (len pre) acc == chars xs (len pre + len (utf8.encode (escape_char c))) (c :: acc)
    proof
        match c
            c'"'  -> auto
            c'\\' -> auto
            c'\n' -> auto
            c'\r' -> auto
            c'\t' -> auto
            _ if char.code c < 0x20 ->
                have hex4_round (char.code c) (pre ++ b"\\u") post
                auto
            _     ->
                have string.from_char_bytes c
                have utf8.decode_from_char c pre post
                auto

# Induction over the characters; the recursive `have` is the induction hypothesis.
lemma chars_render cs acc pre post : cs~List Char, acc~List Char, pre~Bytes, len pre > 0, post~Bytes
    let xs = pre ++ utf8.encode (escaped cs ++ "\"") ++ post
    ensures chars xs (len pre) acc == Ok (string.from_chars (reverse acc ++ cs), len xs - len post)
    proof
        match cs
            []        -> have list.append_nil (reverse acc)
            c :: rest ->
                let e = utf8.encode (escape_char c)
                have escaped cs == escape_char c ++ escaped rest
                have char_step c pre (utf8.encode (escaped rest ++ "\"") ++ post) acc
                have chars_render rest (c :: acc) (pre ++ e) post
                have list.reverse_cons_append acc c rest

# A quoted string is read back as its token, whatever follows it.
lemma string_token_render s post : s~String, post~Bytes
    let xs = utf8.encode (quote s) ++ post
    ensures read_token xs == Ok (StringToken s, post)
    proof
        have string.concat_map_chars escape_char s
        have string.from_chars_chars s
        have chars_render (string.chars s) [] b"\"" post
        have rest_from_append (utf8.encode (quote s)) post

# ── Objects' text ────────────────────────────────────────────────────────────

# One member as `render` writes it, and its depth as `depth` counts it.
fn member_text kx -> s : kx~(String, Json), s~String
    let (k, x) = kx
    quote k ++ ":" ++ render x

fn member_depth kx -> n : kx~(String, Json), n~Nat
    let (_, x) = kx
    depth x

lemma map_member_text fields : fields~List (String, Json)
    ensures map (\(k, x) -> quote k ++ ":" ++ render x) fields == map member_text fields
    proof
        match fields
            []        -> auto
            _ :: rest -> have map_member_text rest

lemma map_member_depth fields : fields~List (String, Json)
    ensures map (\(_, x) -> depth x) fields == map member_depth fields
    proof
        match fields
            []        -> auto
            _ :: rest -> have map_member_depth rest

# A quoted string starts with its quote.
lemma quote_first s : s~String
    let b = utf8.encode (quote s)
    ensures len b > 0 and b[0] == '"'
    proof
        auto

# ── Tokens read as values ────────────────────────────────────────────────────

# Tokens of a value are more than what follows them.
lemma tokens_size v at tail : v~Json, at~Nat, tail~Tokens
    ensures Seq.size (tokens_of v at tail) > Seq.size tail
    proof
        match v
            Arr items  -> have items_size items (at + 1) tail
            Obj fields -> have fields_size fields (at + 1) tail
            _          -> auto

lemma items_size items at tail : items~List Json, at~Nat, tail~Tokens
    ensures Seq.size (items_of items at tail) > Seq.size tail
    proof
        match items
            []        -> auto
            x :: rest ->
                let e = at + width x
                match rest
                    [] -> have tokens_size x at (More (Located e EndArray) tail)
                    _  ->
                        have items_size rest (e + 1) tail
                        have tokens_size x at (More (Located e ValueSeparator) (items_of rest (e + 1) tail))

lemma fields_size fields at tail : fields~List (String, Json), at~Nat, tail~Tokens
    ensures Seq.size (fields_of fields at tail) > Seq.size tail
    proof
        match fields
            []             -> auto
            (k, x) :: rest ->
                let c = at + len (utf8.encode (quote k))
                let e = c + 1 + width x
                match rest
                    [] -> have tokens_size x (c + 1) (More (Located e EndObject) tail)
                    _  ->
                        have fields_size rest (e + 1) tail
                        have tokens_size x (c + 1) (More (Located e ValueSeparator) (fields_of rest (e + 1) tail))

# A value's tokens are read as it, whatever follows them.
lemma build v at tail : v~Json, at~Nat, tail~Tokens
    ensures fix (\zs self -> value self zs zs) (tokens_of v at tail) == Ok (v, tail)
    proof
        let ts = tokens_of v at tail
        have fix_unfold (\zs self -> value self zs zs) ts
        match v
            Arr items  ->
                match items
                    []        -> auto
                    x :: rest ->
                        have tokens_size v at tail
                        have reverse [] ++ items == items
                        have build_items x rest [] (at + 1) tail ts
                        let inner = items_of items (at + 1) tail
                        have array (\ys -> fix (\zs self -> value self zs zs) ys) ts inner
                             == elements (\ys -> fix (\zs self -> value self zs zs) ys) ts inner []
            Obj fields ->
                match fields
                    []             -> auto
                    (k, x) :: rest ->
                        have tokens_size v at tail
                        have reverse [] ++ fields == fields
                        have build_fields k x rest [] (at + 1) tail ts
                        let inner = fields_of fields (at + 1) tail
                        have object (\ys -> fix (\zs self -> value self zs zs) ys) ts inner
                             == members (\ys -> fix (\zs self -> value self zs zs) ys) ts inner []
            _          -> auto

# An array's items' tokens, as `elements` reads them after those in `acc`.
lemma build_items x rest acc at tail top : x~Json, rest~List Json, acc~List Json, at~Nat, tail~Tokens, top~Tokens,
                                           Seq.size (items_of (x :: rest) at tail) < Seq.size top
    ensures elements (\ys -> fix (\zs self -> value self zs zs) ys) top (items_of (x :: rest) at tail) acc
         == Ok (reverse acc ++ (x :: rest), tail)
    proof
        let e = at + width x
        have list.reverse_cons_append acc x rest
        match rest
            []          ->
                let xs = tokens_of x at (More (Located e EndArray) tail)
                have build x at (More (Located e EndArray) tail)
                have elements_last xs acc top x e tail
                have list.append_nil (reverse (x :: acc))
            y :: others ->
                let more = items_of rest (e + 1) tail
                let xs = tokens_of x at (More (Located e ValueSeparator) more)
                have build x at (More (Located e ValueSeparator) more)
                have tokens_size x at (More (Located e ValueSeparator) more)
                have elements_next xs acc top x e more
                have build_items y others (x :: acc) (e + 1) tail top

# `elements` reading an item followed by `,`.
lemma elements_next xs acc top x e more : xs~Tokens, acc~List Json, top~Tokens, Seq.size xs < Seq.size top, x~Json,
                                          e~Nat, more~Tokens,
                                          fix (\zs self -> value self zs zs) xs == Ok (x, More (Located e ValueSeparator) more)
    ensures elements (\ys -> fix (\zs self -> value self zs zs) ys) top xs acc
         == elements (\ys -> fix (\zs self -> value self zs zs) ys) top more (x :: acc)
    proof
        auto

# `elements` reading an item followed by `]`.
lemma elements_last xs acc top x e tail : xs~Tokens, acc~List Json, top~Tokens, Seq.size xs < Seq.size top, x~Json,
                                          e~Nat, tail~Tokens,
                                          fix (\zs self -> value self zs zs) xs == Ok (x, More (Located e EndArray) tail)
    ensures elements (\ys -> fix (\zs self -> value self zs zs) ys) top xs acc == Ok (reverse (x :: acc), tail)
    proof
        auto

# An object's members' tokens, as `members` reads them after those in `acc`.
# Every key is new: `unique` holds of all the keys, those read so far and
# those to come.
lemma build_fields k x rest acc at tail top : k~String, x~Json, rest~List (String, Json), acc~Members,
                                              unique (keys (reverse acc ++ ((k, x) :: rest))), at~Nat, tail~Tokens,
                                              top~Tokens, Seq.size (fields_of ((k, x) :: rest) at tail) < Seq.size top
    ensures members (\ys -> fix (\zs self -> value self zs zs) ys) top (fields_of ((k, x) :: rest) at tail) acc
         == Ok (reverse acc ++ ((k, x) :: rest), tail)
    proof
        have list.keys_append (reverse acc) ((k, x) :: rest)
        have list.unique_split (keys (reverse acc)) k (keys rest)
        have list.keys_reverse acc
        have list.contains_reverse (keys acc) k
        have not (list.contains (keys acc) k)
        have list.reverse_cons_append acc (k, x) rest
        let c = at + len (utf8.encode (quote k))
        let e = c + 1 + width x
        match rest
            []                 ->
                let inner = tokens_of x (c + 1) (More (Located e EndObject) tail)
                have build x (c + 1) (More (Located e EndObject) tail)
                have members_last k inner acc top x e tail at c
                have list.append_nil (reverse ((k, x) :: acc))
            (k2, x2) :: others ->
                let more = fields_of rest (e + 1) tail
                let inner = tokens_of x (c + 1) (More (Located e ValueSeparator) more)
                have build x (c + 1) (More (Located e ValueSeparator) more)
                have tokens_size x (c + 1) (More (Located e ValueSeparator) more)
                have members_next k inner acc top x e more at c
                have build_fields k2 x2 others ((k, x) :: acc) (e + 1) tail top

# `members` reading a new key, `:`, and a value followed by `,`.
lemma members_next k inner acc top x e more at c
    : k~String, inner~Tokens, acc~Members, not (contains (keys acc) k), top~Tokens, x~Json, e~Nat, more~Tokens,
      at~Nat, c~Nat, Seq.size (More (Located at (StringToken k)) (More (Located c NameSeparator) inner)) < Seq.size top,
      fix (\zs self -> value self zs zs) inner == Ok (x, More (Located e ValueSeparator) more)
    let xs = More (Located at (StringToken k)) (More (Located c NameSeparator) inner)
    ensures members (\ys -> fix (\zs self -> value self zs zs) ys) top xs acc
         == members (\ys -> fix (\zs self -> value self zs zs) ys) top more ((k, x) :: acc)
    proof
        have list.unique_cons k (keys acc)

# `members` reading a new key, `:`, and a value followed by `}`.
lemma members_last k inner acc top x e tail at c
    : k~String, inner~Tokens, acc~Members, not (contains (keys acc) k), top~Tokens, x~Json, e~Nat, tail~Tokens,
      at~Nat, c~Nat, Seq.size (More (Located at (StringToken k)) (More (Located c NameSeparator) inner)) < Seq.size top,
      fix (\zs self -> value self zs zs) inner == Ok (x, More (Located e EndObject) tail)
    let xs = More (Located at (StringToken k)) (More (Located c NameSeparator) inner)
    ensures members (\ys -> fix (\zs self -> value self zs zs) ys) top xs acc
         == Ok (reverse ((k, x) :: acc), tail)
    proof
        have list.unique_cons k (keys acc)
        have list.keys_reverse ((k, x) :: acc)
        have list.unique_reverse (keys ((k, x) :: acc))

# ── The round trip ───────────────────────────────────────────────────────────

# The headline theorem. The depth precondition is not decoration: without it the
# statement is false, because parse rejects nesting deeper than MAX_DEPTH.
export lemma roundtrip v : v~Json, depth v <= MAX_DEPTH
    ensures parse (utf8.encode (render v)) == Ok v
    proof
        let src = utf8.encode (render v)
        have lex_value v b"" (len src) 0
        have build v 0 End
        have Parsable.parse (tokens_of v 0 End) Json JsonToken == Ok (v, End)

# ── Compile-time checks ──────────────────────────────────────────────────────
# Evaluated by the compiler; a failing `check` is a compile error.

check parse b"[1, true, \"a\\u00e9\"]"
      == Ok (Arr [Num (decimal.of_int 1), Bool True, Str "aé"])
check parse b"{\"a\":1,\"a\":2}" == Err (Error 7 (DuplicateKey "a"))
check parse b"[1,]" == Err (Error 3 (UnexpectedByte ']'))
check parse b"\"\\ud800\"" == Err (Error 7 BadEscape)
