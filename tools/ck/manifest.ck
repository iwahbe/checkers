# manifest.ck — reading `checkers.json` and `checkers.lock` (SPEC §16.4,
# D107, D111). A problem is reported at its line and column.

module ck.manifest

import std.json (Json, ErrorKind)
import std.string
import std.bytes
import std.char
import std.list (contains)

export record Version
    major~Nat
    minor~Nat
    patch~Nat

export enum Source
    Git url version : url~String, version~Version
    Path dir        : dir~String

export record Dep
    name~String
    source~Source

export record Manifest
    name~String
    toolchain~Version
    deps~List Dep

# What `checkers.lock` records about one package of the build.
export enum Pinned
    PinnedGit url version commit : url~String, version~Version, commit~String
    PinnedPath dir               : dir~String

export record Locked
    name~String
    pin~Pinned

# A problem in a JSON file: the byte it is at, and what it is.
export record Problem
    pos~Nat
    message~String

# ── Versions ─────────────────────────────────────────────────────────────────

# The number written at `b[i]`, and the position after it.
partial fn number b i n seen -> r : b~Bytes, i~Nat, n~Nat, seen~Bool, r~Option (Nat, Nat)
    if i < len b and b[i] >= '0' and b[i] <= '9'
        number b (i + 1) (n * 10 + (b[i] - '0')) True
    else if seen
        Some (n, i)
    else
        None

# `n.` at `b[i]`: the number and the position after the dot.
partial fn part b i -> r : b~Bytes, i~Nat, r~Option (Nat, Nat)
    match number b i 0 False
        Some (n, j) -> if j < len b and b[j] == '.' then Some (n, j + 1) else None
        None        -> None

# `MAJOR.MINOR.PATCH`.
export partial fn parse_version s -> r : s~String, r~Option Version
    let b = string.bytes s
    match part b 0
        None        -> None
        Some (x, i) ->
            match part b i
                None        -> None
                Some (y, j) ->
                    match number b j 0 False
                        Some (z, k) -> if k == len b then Some (Version x y z) else None
                        None        -> None

export fn show v -> s : v~Version, s~String
    format v.major ++ "." ++ format v.minor ++ "." ++ format v.patch

export fn older a b -> r : a~Version, b~Version, r~Bool
    a.major < b.major
        or (a.major == b.major and (a.minor < b.minor or (a.minor == b.minor and a.patch < b.patch)))

# ── Positions ────────────────────────────────────────────────────────────────

fn blank c : c~U8
    c == ' ' or c == '\n' or c == '\r' or c == '\t'

partial fn space b i -> r : b~Bytes, i~Nat, r~Nat
    if i < len b and blank b[i] then space b (i + 1) else i

# The position after a string whose contents start at `i`.
partial fn after_string b i -> r : b~Bytes, i~Nat, r~Nat
    if i >= len b
        i
    else if b[i] == '\\'
        after_string b (i + 2)
    else if b[i] == '"'
        i + 1
    else
        after_string b (i + 1)

# The position after the value at `i`, nested `d` deep (the file is valid JSON).
partial fn skip b i d -> r : b~Bytes, i~Nat, d~Nat, r~Nat
    if i >= len b
        i
    else if b[i] == '"'
        let j = after_string b (i + 1)
        if d == 0 then j else skip b j d
    else if b[i] == '{' or b[i] == '['
        skip b (i + 1) (d + 1)
    else if b[i] == '}' or b[i] == ']'
        if d == 0 then i else if d == 1 then i + 1 else skip b (i + 1) (d - 1)
    else if d == 0 and (b[i] == ',' or blank b[i])
        i
    else
        skip b (i + 1) d

# The member `key` of the object at `i`: where its key and its value start.
partial fn member b i key -> r : b~Bytes, i~Nat, key~Bytes, r~Option (Nat, Nat)
    if i < len b and b[i] == '{' then members b (space b (i + 1)) key else None

partial fn members b i key -> r : b~Bytes, i~Nat, key~Bytes, r~Option (Nat, Nat)
    if i < len b and b[i] == '"'
        let close = after_string b (i + 1)
        let v = space b (space b close + 1)
        if close == i + len key + 2 and bytes.matches_at b (i + 1) key
            Some (i, v)
        else
            let next = space b (skip b v 0)
            if next < len b and b[next] == ',' then members b (space b (next + 1)) key else None
    else
        None

partial fn find b i path last -> r : b~Bytes, i~Nat, path~List String, last~Nat, r~Nat
    match path
        []        -> last
        k :: rest ->
            match member b i (string.bytes k)
                Some (at, v) -> find b v rest at
                None         -> last

# Where the member at `path` is written in `src`: its key (the start of the
# file for `[]`, the nearest enclosing member if there is none).
export partial fn locate src path -> pos : src~Bytes, path~List String, pos~Nat
    find src (space src 0) path (space src 0)

# Line and column (from 1) of byte `pos`.
fn lines src pos i line col -> r : src~Bytes, pos~Nat, i~Nat, i <= len src, line~Nat, col~Nat,
                                   r~(Nat, Nat)
    decreasing len src - i
    if i >= pos or i >= len src
        (line, col)
    else if src[i] == '\n'
        lines src pos (i + 1) (line + 1) 1
    else
        lines src pos (i + 1) line (col + 1)

# `FILE:LINE:COL: message`.
export fn describe file src p -> s : file~String, src~Bytes, p~Problem, s~String
    let (line, col) = lines src p.pos 0 1 1
    file ++ ":" ++ format line ++ ":" ++ format col ++ ": " ++ p.message

# ── Reading ──────────────────────────────────────────────────────────────────

# A byte as it reads: `'}'`, or its number if it isn't printable ASCII.
fn shown b -> s : b~U8, s~String
    if b >= 0x20 and b < 0x7F then "`" ++ string.from_char (char.from_ascii b) ++ "`" else "byte " ++ format b

fn syntax k -> s : k~ErrorKind, s~String
    match k
        UnexpectedEnd    -> "the file ends too soon"
        UnexpectedByte b -> "unexpected " ++ shown b
        BadEscape        -> "a bad escape sequence"
        BadUtf8          -> "bytes that are not UTF-8"
        ControlInString  -> "a control character in a string"
        DuplicateKey k   -> "`" ++ k ++ "` appears twice"
        TooDeep          -> "nested too deeply"
        TrailingInput    -> "more after the end of the JSON value"

partial fn field fields k -> r : fields~List (String, Json), k~String, r~Option Json
    match fields
        []             -> None
        (n, v) :: rest -> if n == k then Some v else field rest k

# The first key of `fields` not in `known`.
partial fn unknown fields known -> r : fields~List (String, Json), known~List String, r~Option String
    match fields
        []             -> None
        (n, _) :: rest -> if contains known n then unknown rest known else Some n

fn name_byte c first : c~U8, first~Bool
    (c >= 'a' and c <= 'z') or (not first and ((c >= '0' and c <= '9') or c == '_'))

fn name_from b i -> r : b~Bytes, i~Nat, i <= len b, r~Bool
    decreasing len b - i
    if i >= len b then True else name_byte b[i] (i == 0) and name_from b (i + 1)

# Lower-case letters, digits and `_`, starting with a letter.
export fn valid_name s -> r : s~String, r~Bool
    let b = string.bytes s
    len b > 0 and name_from b 0

partial fn at src path msg -> r : src~Bytes, path~List String, msg~String, r~Problem
    Problem (locate src path) msg

partial fn string_field src fields path k -> r : src~Bytes, fields~List (String, Json),
                                                 path~List String, k~String,
                                                 r~Result String Problem
    match field fields k
        Some (Str s) -> Ok s
        Some _       -> Err (at src (path ++ [k]) ("`" ++ k ++ "` must be a string"))
        None         -> Err (at src path ("`" ++ k ++ "` is missing"))

partial fn version_field src fields path k -> r : src~Bytes, fields~List (String, Json),
                                                  path~List String, k~String,
                                                  r~Result Version Problem
    match string_field src fields path k
        Err p -> Err p
        Ok s  ->
            match parse_version s
                Some v -> Ok v
                None   -> Err (at src (path ++ [k]) ("`" ++ k ++ "` must be MAJOR.MINOR.PATCH, like 1.2.0"))

partial fn dep src name spec -> r : src~Bytes, name~String, spec~Json, r~Result Dep Problem
    let path = ["dependencies", name]
    if not (valid_name name) or name == "std"
        Err (at src path ("`" ++ name ++ "` isn't a package name: lower-case letters, digits and `_`, starting with a letter; not `std`"))
    else
        match spec
            Obj fs ->
                match unknown fs ["git", "version", "path"]
                    Some k -> Err (at src (path ++ [k]) ("unknown field `" ++ k ++ "`: a dependency has `git` and `version`, or `path`"))
                    None   -> dep_source src name path fs
            _      -> Err (at src path ("`" ++ name ++ "` must be an object: { \"git\": URL, \"version\": \"1.2.0\" } or { \"path\": DIR }"))

partial fn dep_source src name path fs -> r : src~Bytes, name~String, path~List String,
                                              fs~List (String, Json), r~Result Dep Problem
    match (field fs "git", field fs "path")
        (Some _, Some _) -> Err (at src path ("`" ++ name ++ "` has both `git` and `path`"))
        (None, None)     -> Err (at src path ("`" ++ name ++ "` needs `git` and `version`, or `path`"))
        (None, Some _)   ->
            if field fs "version" != None
                Err (at src (path ++ ["version"]) "a path dependency has no `version`: it is used as it is")
            else
                match string_field src fs path "path"
                    Ok d  -> Ok (Dep name (Path d))
                    Err p -> Err p
        (Some _, None)   ->
            match string_field src fs path "git"
                Err p -> Err p
                Ok u  ->
                    match version_field src fs path "version"
                        Ok v  -> Ok (Dep name (Git u v))
                        Err p -> Err p

partial fn deps src members acc -> r : src~Bytes, members~List (String, Json), acc~List Dep,
                                       r~Result (List Dep) Problem
    match members
        []                -> Ok (list.reverse acc)
        (n, spec) :: rest ->
            match dep src n spec
                Ok d  -> deps src rest (d :: acc)
                Err p -> Err p

partial fn manifest src fields -> r : src~Bytes, fields~List (String, Json), r~Result Manifest Problem
    match unknown fields ["name", "version", "toolchain", "dependencies"]
        Some k -> Err (at src [k] ("unknown field `" ++ k ++ "`: the fields are `name`, `version`, `toolchain` and `dependencies`"))
        None   ->
            match string_field src fields [] "name"
                Err p -> Err p
                Ok n  ->
                    if not (valid_name n) or n == "std"
                        Err (at src ["name"] ("`" ++ n ++ "` isn't a package name: lower-case letters, digits and `_`, starting with a letter; not `std`"))
                    else
                        match (version_field src fields [] "version", version_field src fields [] "toolchain")
                            (Err p, _)    -> Err p
                            (_, Err p)    -> Err p
                            (Ok _, Ok tc) ->
                                match field fields "dependencies"
                                    None          -> Ok (Manifest n tc [])
                                    Some (Obj ms) ->
                                        match deps src ms []
                                            Ok ds -> Ok (Manifest n tc ds)
                                            Err p -> Err p
                                    Some _        -> Err (at src ["dependencies"] "`dependencies` must be an object")

# Read `checkers.json`.
export partial fn read src -> r : src~Bytes, r~Result Manifest Problem
    match json.parse src
        Err e           -> Err (Problem e.pos (syntax e.kind))
        Ok (Obj fields) -> manifest src fields
        Ok _            -> Err (Problem (space src 0) "the manifest must be a JSON object")

# ── The lock file ────────────────────────────────────────────────────────────

partial fn pinned src name spec -> r : src~Bytes, name~String, spec~Json, r~Result Locked Problem
    let path = [name]
    match spec
        Obj fs ->
            match field fs "path"
                Some (Str d) -> Ok (Locked name (PinnedPath d))
                _            ->
                    match (string_field src fs path "git", version_field src fs path "version", string_field src fs path "commit")
                        (Ok u, Ok v, Ok c) -> Ok (Locked name (PinnedGit u v c))
                        (Err p, _, _)      -> Err p
                        (_, Err p, _)      -> Err p
                        (_, _, Err p)      -> Err p
        _      -> Err (at src path ("`" ++ name ++ "` must be an object"))

partial fn pins src members acc -> r : src~Bytes, members~List (String, Json), acc~List Locked,
                                       r~Result (List Locked) Problem
    match members
        []                -> Ok (list.reverse acc)
        (n, spec) :: rest ->
            match pinned src n spec
                Ok l  -> pins src rest (l :: acc)
                Err p -> Err p

# Read `checkers.lock`.
export partial fn read_lock src -> r : src~Bytes, r~Result (List Locked) Problem
    match json.parse src
        Err e           -> Err (Problem e.pos (syntax e.kind))
        Ok (Obj fields) -> pins src fields []
        Ok _            -> Err (Problem (space src 0) "the lock file must be a JSON object")

fn quote s -> q : s~String, q~String
    json.render (Str s)

fn pin_line l -> s : l~Locked, s~String
    let body = match l.pin
        PinnedGit u v c -> "{ \"git\": " ++ quote u ++ ", \"version\": " ++ quote (show v) ++ ", \"commit\": " ++ quote c ++ " }"
        PinnedPath d    -> "{ \"path\": " ++ quote d ++ " }"
    "  " ++ quote l.name ++ ": " ++ body

# `checkers.lock`'s text, one package per line, in the order given.
export fn render_lock ls -> s : ls~List Locked, s~String
    match ls
        [] -> "{}\n"
        _  -> "{\n" ++ list.join ",\n" (list.map pin_line ls) ++ "\n}\n"
