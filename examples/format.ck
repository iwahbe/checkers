# format.ck — a typed `fmt`, staged at compile time (SPEC §8.9, milestone M6).
#
# `fmt "{} is {n} years old"` has type `String -> Int -> String`: the
# format string is a `comptime` parameter, so its placeholders are known
# while type checking, and `format_type` turns them into a function type.
# Staging then expands `go` over the pieces: what runs is a chain of `++`,
# with no format string left to parse (`checkers stage format.ck` shows it).
# A placeholder other than `{}` and `{n}` is an error at the call.

module format

import system (System, ExitCode)
import terminal (Term)
import list (reverse)
import char
import string

# A format string, taken apart: `{}` takes a String, `{n}` an Int.
export enum Piece
    Text s : s~String
    Str
    Num
    Bad                     # a `{` or `}` that isn't part of a placeholder

# What `fmt` gives a bad format string, so the type error says why.
export enum BadPlaceholder
    Rejected

# The type `fmt` gives a format string: one parameter per placeholder.
export transparent fn format_type ps -> t : ps~List Piece, t~Type
    match ps
        []             -> String
        Text _ :: rest -> format_type rest
        Str :: rest    -> String -> format_type rest
        Num :: rest    -> Int -> format_type rest
        Bad :: _       -> BadPlaceholder

# Every `{` starts `{}` or `{n}`, and every `}` ends one.
export transparent fn valid src i -> b : src~Bytes, i~Nat, i <= len src, b~Bool
    decreasing len src - i
    if i == len src
        True
    else if src[i] == '{' and i + 1 < len src and src[i + 1] == '}'
        valid src (i + 2)
    else if src[i] == '{' and i + 2 < len src and src[i + 1] == 'n' and src[i + 2] == '}'
        valid src (i + 3)
    else if src[i] == '{' or src[i] == '}'
        False
    else
        valid src (i + 1)

# The pieces of src[i..]; `text` is the current Text piece so far, reversed.
export transparent fn pieces src i text -> ps : src~Bytes, i~Nat, i <= len src, text~List Char, ps~List Piece
    decreasing len src - i
    if i == len src
        flush text []
    else if src[i] == '{' and i + 1 < len src and src[i + 1] == '}'
        flush text (Str :: pieces src (i + 2) [])
    else if src[i] == '{' and i + 2 < len src and src[i + 1] == 'n' and src[i + 2] == '}'
        flush text (Num :: pieces src (i + 3) [])
    else if src[i] == '{' or src[i] == '}'
        flush text [Bad]
    else if src[i] < 128
        pieces src (i + 1) (char.from_ascii src[i] :: text)
    else
        pieces src (i + 1) text                   # ASCII only, to keep the example short

fn flush text rest -> ps : text~List Char, rest~List Piece, ps~List Piece
    match text
        [] -> rest
        _  -> Text (string.from_chars (reverse text)) :: rest

# Expanded at compile time, piece by piece: each placeholder becomes a lambda.
fn go ps acc -> f : ps~comptime List Piece, acc~String, f~format_type ps
    match ps
        []             -> acc
        Text t :: rest -> go rest (acc ++ t)
        Str :: rest    -> \x -> go rest (acc ++ x)
        Num :: rest    -> \n -> go rest (acc ++ format n)
        Bad :: _       -> Rejected

export fn fmt s -> f : s~comptime String, valid (string.bytes s) 0,
                       f~format_type (pieces (string.bytes s) 0 [])
    go (pieces (string.bytes s) 0 []) ""

fn greet name age -> s : name~String, age~Int, s~String
    fmt "{} is {n} years old" name age

check greet "Ada" 36 == "Ada is 36 years old"
check fmt "{n} + {n} = {n}" 1 2 3 == "1 + 2 = 3"
check fmt "no placeholders" == "no placeholders"

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (greet "Ada" 36) sys.term
    Success
