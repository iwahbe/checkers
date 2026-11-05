# json.ck — RFC 8259 JSON parser and renderer, with a round-trip proof.
#
# Design example for SPEC.md §9. Proof bodies are illustrative until the
# prover lands (M3–M5).
#
# What the compiler proves about this file (nothing here is a runtime check):
#   • every byte access src[i] is in bounds            (refinements on i)
#   • the parser terminates on every input             (`decreasing` + Parsed's start < stop)
#   • every Err position points inside the input       (Error's invariant)
#   • a Json object can never hold duplicate keys      (Obj's constructor invariant)
#   • parse (render v) == Ok v for every v within the depth limit   (lemma `roundtrip`)

module json

import cursor (Parsed)            # record Parsed a src start: a value plus the position after it
import decimal (Decimal)          # sealed: exact decimal numbers, JSON number scanning/rendering
import utf8                       # sealed: decode_at, encode, and their lemmas
import bytes                      # sealed: matches_at, ...
import list (keys, unique, contains, reverse, join, map, max_of)   # `keys` is exported transparent

# ── Data ─────────────────────────────────────────────────────────────────────

export enum Json
    Null
    Bool b      : b~Bool
    Num n       : n~Decimal
    Str s       : s~String
    Arr items   : items~List Json
    Obj fields  : fields~List (String, Json), unique (keys fields)

# Object members. Insertion order is kept; duplicates are unrepresentable.
type Members = fs~List (String, Json), unique (keys fs)

export enum ErrorKind
    UnexpectedEnd
    UnexpectedByte b    : b~U8
    BadEscape
    BadUtf8
    ControlInString
    DuplicateKey k      : k~String
    TooDeep
    TrailingInput

# An error always points into the input it came from. `src` is ghost: it
# exists only in the type, so Error costs one Nat and one tag at runtime.
export record Error src : src~ghost Bytes
    pos~Nat, pos <= len src
    kind~ErrorKind

export let MAX_DEPTH = 512

export fn depth v -> d : v~Json, d~Nat
    match v
        Arr items  -> 1 + max_of (map depth items)
        Obj fields -> 1 + max_of (map (\(_, x) -> depth x) fields)
        _          -> 0

# ── Parsing ──────────────────────────────────────────────────────────────────

export fn parse src -> r : src~Bytes, r~Result Json (Error src)
    let v = try value src (skip_ws src 0) 0
    let end = skip_ws src v.stop
    if end == len src then Ok v.value else Err (Error end TrailingInput)

# No postcondition needed: inside this module the solver can see the body.
fn peek src i -> r : src~Bytes, i~Nat, r~Option U8
    if i < len src then Some src[i] else None

fn is_ws b : b~U8
    b == ' ' or b == '\t' or b == '\n' or b == '\r'

fn skip_ws src i -> j : src~Bytes, i~Nat, i <= len src,
                        j~Nat, i <= j, j <= len src
    decreasing len src - i
    if i < len src and is_ws src[i]        # src[i] is safe: `and` short-circuits
        skip_ws src (i + 1)
    else
        i

# Measures are lexicographic. value → array/object strictly advances i;
# array/object → elements/members → value may stay at the same i, so the
# second component (2 → 1 → 0) does the decreasing there.
fn value src i depth -> r : src~Bytes, i~Nat, i <= len src, depth~Nat,
                            r~Result (Parsed Json src i) (Error src)
    decreasing (len src - i, 0)
    match peek src i
        None     -> Err (Error i UnexpectedEnd)
        Some 'n' -> literal src i b"null" Null
        Some 't' -> literal src i b"true" (Bool True)
        Some 'f' -> literal src i b"false" (Bool False)
        Some '"' ->
            let s = try string_body src (i + 1)
            Ok (Parsed (Str s.value) s.stop)
        Some '[' if depth >= MAX_DEPTH -> Err (Error i TooDeep)
        Some '[' ->
            let a = try array src (i + 1) (depth + 1)
            Ok (Parsed (Arr a.value) a.stop)
        Some '{' if depth >= MAX_DEPTH -> Err (Error i TooDeep)
        Some '{' ->
            let o = try object src (i + 1) (depth + 1)
            Ok (Parsed (Obj o.value) o.stop)       # o.value~Members carries unique (keys …)
        Some b ->
            match decimal.scan_json src i
                Some n -> Ok (Parsed (Num n.value) n.stop)
                None   -> Err (Error i (UnexpectedByte b))

fn literal src i word v -> r : src~Bytes, i~Nat, i < len src,
                               word~Bytes, len word > 0, v~Json,
                               r~Result (Parsed Json src i) (Error src)
    if bytes.matches_at src i word         # exported postcondition: i + len word <= len src
        Ok (Parsed v (i + len word))
    else
        Err (Error i (UnexpectedByte src[i]))

fn array src i depth -> r : src~Bytes, i~Nat, i <= len src, depth~Nat,
                            r~Result (Parsed (List Json) src i) (Error src)
    decreasing (len src - i, 2)
    let j = skip_ws src i
    if peek src j == Some ']'
        Ok (Parsed [] (j + 1))
    else
        elements src i j depth []

fn elements src start k depth acc -> r : src~Bytes, start~Nat, k~Nat, start <= k, k <= len src,
                                         depth~Nat, acc~List Json,
                                         r~Result (Parsed (List Json) src start) (Error src)
    decreasing (len src - k, 1)
    let v = try value src k depth
    let j = skip_ws src v.stop
    match peek src j
        Some ',' -> elements src start (skip_ws src (j + 1)) depth (v.value :: acc)
        Some ']' -> Ok (Parsed (reverse (v.value :: acc)) (j + 1))
        Some b   -> Err (Error j (UnexpectedByte b))
        None     -> Err (Error j UnexpectedEnd)

fn object src i depth -> r : src~Bytes, i~Nat, i <= len src, depth~Nat,
                             r~Result (Parsed Members src i) (Error src)
    decreasing (len src - i, 2)
    let j = skip_ws src i
    if peek src j == Some '}'
        Ok (Parsed [] (j + 1))
    else
        members src i j depth []

fn members src start k depth acc -> r : src~Bytes, start~Nat, k~Nat, start <= k, k <= len src,
                                        depth~Nat, acc~Members,
                                        r~Result (Parsed Members src start) (Error src)
    decreasing (len src - k, 1)
    let key = try quoted src k
    if contains (keys acc) key.value
        Err (Error k (DuplicateKey key.value))
    else
        let colon = try expect src (skip_ws src key.stop) ':'
        let v = try value src (skip_ws src colon.stop) depth
        have list.unique_cons key.value (keys acc)     # ¬contains ∧ unique ⇒ still unique
        let acc2 = (key.value, v.value) :: acc
        let j = skip_ws src v.stop
        match peek src j
            Some ',' -> members src start (skip_ws src (j + 1)) depth acc2
            Some '}' ->
                have list.keys_reverse acc2
                have list.unique_reverse (keys acc2)
                Ok (Parsed (reverse acc2) (j + 1))
            Some b   -> Err (Error j (UnexpectedByte b))
            None     -> Err (Error j UnexpectedEnd)

fn expect src i b -> r : src~Bytes, i~Nat, i <= len src, b~U8,
                         r~Result (Parsed Unit src i) (Error src)
    match peek src i
        Some c if c == b -> Ok (Parsed () (i + 1))
        Some c           -> Err (Error i (UnexpectedByte c))
        None             -> Err (Error i UnexpectedEnd)

fn quoted src k -> r : src~Bytes, k~Nat, k <= len src,
                       r~Result (Parsed String src k) (Error src)
    let q = try expect src k '"'
    let s = try string_body src q.stop
    Ok (Parsed s.value s.stop)

# ── Strings ──────────────────────────────────────────────────────────────────

# `i` points just past the opening quote.
fn string_body src i -> r : src~Bytes, i~Nat, i <= len src,
                            r~Result (Parsed String src i) (Error src)
    chars src i i []

fn chars src start k acc -> r : src~Bytes, start~Nat, k~Nat, start <= k, k <= len src,
                                acc~List Char,
                                r~Result (Parsed String src start) (Error src)
    decreasing len src - k
    match peek src k
        None               -> Err (Error k UnexpectedEnd)
        Some '"'           -> Ok (Parsed (string.from_chars (reverse acc)) (k + 1))
        Some '\\'          ->
            let e = try escape src (k + 1)
            chars src start e.stop (e.value :: acc)
        Some b if b < 0x20 -> Err (Error k ControlInString)
        Some _             ->
            match utf8.decode_at src k            # Parsed Char src k: always advances
                Some c -> chars src start c.stop (c.value :: acc)
                None   -> Err (Error k BadUtf8)

fn escape src i -> r : src~Bytes, i~Nat, i <= len src,
                       r~Result (Parsed Char src i) (Error src)
    match peek src i
        Some '"'  -> Ok (Parsed c'"' (i + 1))
        Some '\\' -> Ok (Parsed c'\\' (i + 1))
        Some '/'  -> Ok (Parsed c'/' (i + 1))
        Some 'b'  -> Ok (Parsed c'\x08' (i + 1))
        Some 'f'  -> Ok (Parsed c'\x0c' (i + 1))
        Some 'n'  -> Ok (Parsed c'\n' (i + 1))
        Some 'r'  -> Ok (Parsed c'\r' (i + 1))
        Some 't'  -> Ok (Parsed c'\t' (i + 1))
        Some 'u'  ->
            let u = try unicode_escape src (i + 1)
            Ok (Parsed u.value u.stop)
        _         -> Err (Error i BadEscape)

type Hex16 = n~Nat, n < 0x10000

fn hex_digit b : b~U8
    ('0' <= b and b <= '9') or ('a' <= b and b <= 'f') or ('A' <= b and b <= 'F')

# U8 is a refinement of Nat (n < 256), so `b - '0'` is Nat subtraction; its
# precondition b >= '0' follows from hex_digit b and the branch taken.
fn hex_value b -> n : b~U8, hex_digit b, n~Nat, n < 16
    if b <= '9' then b - '0' else if b <= 'F' then b - 'A' + 10 else b - 'a' + 10

fn hex4 src i -> r : src~Bytes, i~Nat, i <= len src,
                     r~Result (Parsed Hex16 src i) (Error src)
    if i + 4 <= len src and hex_digit src[i] and hex_digit src[i + 1]
                        and hex_digit src[i + 2] and hex_digit src[i + 3]
        let n = hex_value src[i] * 4096 + hex_value src[i + 1] * 256
              + hex_value src[i + 2] * 16 + hex_value src[i + 3]
        Ok (Parsed n (i + 4))                # n < 0x10000 follows from each digit < 16
    else
        Err (Error i BadEscape)

fn unicode_escape src i -> r : src~Bytes, i~Nat, i <= len src,
                               r~Result (Parsed Char src i) (Error src)
    let hi = try hex4 src i
    if 0xD800 <= hi.value and hi.value < 0xDC00                 # high surrogate: needs a pair
        if bytes.matches_at src hi.stop b"\\u"
            let lo = try hex4 src (hi.stop + 2)
            if 0xDC00 <= lo.value and lo.value < 0xE000
                Ok (Parsed (char.from_surrogates hi.value lo.value) lo.stop)
            else
                Err (Error hi.stop BadEscape)
        else
            Err (Error hi.stop BadEscape)
    else if 0xDC00 <= hi.value and hi.value < 0xE000            # lone low surrogate
        Err (Error i BadEscape)
    else
        Ok (Parsed (char.from_scalar hi.value) hi.stop)         # requires: not a surrogate — proven above

# ── Rendering ────────────────────────────────────────────────────────────────

export fn render v -> s : v~Json, s~String
    match v
        Null        -> "null"
        Bool b      -> if b then "true" else "false"
        Num n       -> decimal.render n
        Str s       -> quote s
        Arr items   -> "[" ++ join "," (map render items) ++ "]"
        Obj fields  -> "{" ++ join "," (map (\(k, x) -> quote k ++ ":" ++ render x) fields) ++ "}"

fn quote s -> q : s~String, q~String
    "\"" ++ string.concat_map escape_char s ++ "\""

fn escape_char c -> s : c~Char, s~String
    match c
        c'"'                     -> "\\\""
        c'\\'                    -> "\\\\"
        c'\n'                    -> "\\n"
        c'\r'                    -> "\\r"
        c'\t'                    -> "\\t"
        _ if char.code c < 0x20  -> "\\u" ++ hex4_string (char.code c)
        _                        -> string.from_char c

fn hex4_string n -> s : n~Nat, n < 0x10000, s~String
    let digit = \d -> char.from_ascii b"0123456789abcdef"[d]     # d < 16 ⇒ index in bounds
    string.from_chars [digit (n / 4096), digit (n / 256 % 16), digit (n / 16 % 16), digit (n % 16)]

# ── Proofs ───────────────────────────────────────────────────────────────────

# Bytes that may legally follow a JSON value.
fn delimits post : post~Bytes
    len post == 0 or is_ws post[0] or post[0] == ',' or post[0] == ']' or post[0] == '}'

# The headline theorem. The depth precondition is not decoration: without it the
# statement is false, because parse rejects nesting deeper than MAX_DEPTH.
export lemma roundtrip v : v~Json, depth v <= MAX_DEPTH
    ensures parse (utf8.encode (render v)) == Ok v
    proof
        have value_render v b"" b"" 0

# Generalized so it can be used inside larger documents: any prefix, any
# delimiting suffix, any starting depth.
lemma value_render v pre post d : v~Json, pre~Bytes, post~Bytes, delimits post,
                                  d~Nat, d + depth v <= MAX_DEPTH
    let src = pre ++ utf8.encode (render v) ++ post
    ensures value src (len pre) d == Ok (Parsed v (len src - len post))
    proof
        match v
            Null | Bool _ -> auto                                    # unfold value/literal/render; solver closes
            Num n         -> have decimal.scan_json_render n pre post
            Str s         -> have string_render s pre post d
            Arr []        -> auto
            Arr items     ->
                let pre2 = pre ++ b"["
                have utf8.encode_append "[" (join "," (map render items) ++ "]")
                have elements_render items [] pre2 post (len pre2) (d + 1)
            Obj fields    -> have members_render fields pre post d

# Induction over the remaining items; the recursive `have` is the induction hypothesis.
lemma elements_render items acc pre post start d
    : items~List Json, items != [], acc~List Json,
      pre~Bytes, post~Bytes, delimits post, start~Nat, start <= len pre,
      d~Nat, d + max_of (map depth items) <= MAX_DEPTH
    let src = pre ++ utf8.encode (join "," (map render items) ++ "]") ++ post
    ensures elements src start (len pre) d acc
         == Ok (Parsed (reverse acc ++ items) (len src - len post))
    proof
        match items
            [x] ->
                have value_render x pre (b"]" ++ post) d
            x :: rest ->                                             # first-match: rest != [] here
                let pre2 = pre ++ utf8.encode (render x) ++ b","
                have utf8.encode_append (render x ++ ",") (join "," (map render rest) ++ "]")
                have value_render x pre (b"," ++ utf8.encode (join "," (map render rest) ++ "]") ++ post) d
                have elements_render rest (x :: acc) pre2 post start d
                have list.reverse_cons_append acc x rest

# Not yet proven. `admit` is legal but recorded in the trust ledger (SPEC §7.4),
# so `checkers trust json` lists both until they are discharged.
lemma string_render s pre post d : s~String, pre~Bytes, post~Bytes, delimits post, d~Nat
    let src = pre ++ utf8.encode (quote s) ++ post
    ensures value src (len pre) d == Ok (Parsed (Str s) (len src - len post))
    proof
        admit

lemma members_render fields pre post d : fields~Members, pre~Bytes, post~Bytes, delimits post,
                                         d~Nat, d + depth (Obj fields) <= MAX_DEPTH
    let src = pre ++ utf8.encode (render (Obj fields)) ++ post
    ensures value src (len pre) d == Ok (Parsed (Obj fields) (len src - len post))
    proof
        admit

# ── Compile-time checks ──────────────────────────────────────────────────────
# Evaluated by the compiler; a failing `check` is a compile error.

check parse b"[1, true, \"a\\u00e9\"]"
      == Ok (Arr [Num (decimal.of_int 1), Bool True, Str "aé"])
check parse b"{\"a\":1,\"a\":2}" == Err (Error 7 (DuplicateKey "a"))
check parse b"[1,]" == Err (Error 3 (UnexpectedByte ']'))
check parse b"\"\\ud800\"" == Err (Error 7 BadEscape)
