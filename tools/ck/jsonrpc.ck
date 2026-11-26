# jsonrpc.ck — messages of the language server protocol (SPEC §15.5): each
# is a JSON value after a `Content-Length` header, on a stream.

module ck.jsonrpc

import std.files (File, IoError)
import std.json (Json, Null, Bool, Num, Str, Arr, Obj)
import std.decimal
import std.string
import std.bytes
import std.list (keys, unique)
import ck.text
import std.list

# ── Numbers ──────────────────────────────────────────────────────────────────

# The number that is all of `b`, if `b` is one or more digits.
fn whole b -> r : b~Bytes, r~Option Nat
    match text.natural b
        Some (n, rest) -> if len rest == 0 then Some n else None
        None           -> None

# A whole number, as a `Nat`.
export fn nat_of j -> r : j~Json, r~Option Nat
    match j
        Num d -> whole (string.bytes (decimal.render d))
        _     -> None

export fn num n -> j : n~Nat, j~Json
    Num (decimal.of_int n)

# ── Objects ──────────────────────────────────────────────────────────────────

# The value of `key` in an object.
export partial fn get key j -> r : key~String, j~Json, r~Option Json
    match j
        Obj fields -> find key fields
        _          -> None

partial fn find key fields -> r : key~String, fields~List (String, Json), r~Option Json
    match fields
        []             -> None
        (k, v) :: rest -> if k == key then Some v else find key rest

# The value at a path of keys.
export partial fn at keys j -> r : keys~List String, j~Json, r~Option Json
    match keys
        []        -> Some j
        k :: rest ->
            match get k j
                Some v -> at rest v
                None   -> None

export partial fn str_at keys j -> r : keys~List String, j~Json, r~Option String
    match at keys j
        Some (Str s) -> Some s
        _            -> None

export partial fn nat_at keys j -> r : keys~List String, j~Json, r~Option Nat
    match at keys j
        Some v -> nat_of v
        None   -> None

# An object from pairs whose keys are known to differ; a repeated key keeps
# its first value.
export partial fn obj pairs -> j : pairs~List (String, Json), j~Json
    Obj (dedup pairs [])

partial fn dedup pairs seen -> r : pairs~List (String, Json), seen~List (String, Json),
                                   r~(fs~List (String, Json), unique (keys fs))
    match pairs
        []             -> unique_of (list.reverse seen)
        (k, v) :: rest ->
            if list.contains (keys seen) k then dedup rest seen else dedup rest ((k, v) :: seen)

# Checked at run time: the pairs, if their keys differ, else none of them.
fn unique_of ps -> r : ps~List (String, Json), r~(fs~List (String, Json), unique (keys fs))
    if list.unique (keys ps) then ps else []

# ── Messages ─────────────────────────────────────────────────────────────────

fn starts_with b prefix : b~Bytes, prefix~Bytes
    bytes.matches_at b 0 prefix

fn trimmed_end b -> r : b~Bytes, r~Bytes
    decreasing len b
    if len b > 0 and (b[len b - 1] == '\r' or b[len b - 1] == ' ')
        trimmed_end (bytes.slice b 0 (len b - 1))
    else
        b

# The `Content-Length` of a header line, if it is that header.
fn content_length line -> r : line~Bytes, r~Option Nat
    let b = trimmed_end line
    let name = b"Content-Length:"
    if starts_with b name
        whole (skip_spaces (bytes.slice b (len name) (len b)))
    else
        None

# `b` without the spaces at its start.
fn skip_spaces b -> r : b~Bytes, r~Bytes
    match b
        x :: rest -> if x == ' ' then skip_spaces rest else b
        []        -> b

# What reading a message gave.
export enum Incoming
    Message m     : m~Json
    Malformed why : why~String
    Closed

# Read the headers up to the blank line: the content length, if one was given.
partial fn headers found f -> r : found~Option Nat, f~File, r~(Option (Option Nat), File)
    let (line, f) = files.read_line f
    match line
        # The stream can't be read any further, as for a body that can't.
        Err _       -> (None, f)
        Ok None     -> (None, f)
        Ok (Some l) ->
            let b = trimmed_end l
            if len b == 0
                (Some found, f)
            else
                match content_length l
                    Some n -> headers (Some n) f
                    None   -> headers found f

# The next message on `f`.
export partial fn read f -> r : f~File, r~(Incoming, File)
    let (h, f) = headers None f
    match h
        None          -> (Closed, f)
        Some None     -> (Malformed "a message without a Content-Length header", f)
        Some (Some n) ->
            let (body, f) = files.read_exactly n f
            match body
                Err _ -> (Closed, f)
                Ok b  ->
                    match json.parse b
                        Ok v  -> (Message v, f)
                        Err _ -> (Malformed "a message that isn't JSON", f)

# Write `v` as a message, at once: the client is waiting for it.
export fn write v f -> r : v~Json, f~File, r~(Result Unit IoError, File)
    let body = string.bytes (json.render v)
    let head = string.bytes string.format"Content-Length: {len body}\r\n\r\n"
    let (w, f) = files.write_bytes (bytes.concat [head, body]) f
    match w
        Ok _  -> files.flush f
        Err e -> (Err e, f)

export partial fn response id result -> j : id~Json, result~Json, j~Json
    obj [("jsonrpc", Str "2.0"), ("id", id), ("result", result)]

export partial fn error_response id code message -> j : id~Json, code~Int, message~String, j~Json
    let e = obj [("code", Num (decimal.of_int code)), ("message", Str message)]
    obj [("jsonrpc", Str "2.0"), ("id", id), ("error", e)]

export partial fn notification method params -> j : method~String, params~Json, j~Json
    obj [("jsonrpc", Str "2.0"), ("method", Str method), ("params", params)]
