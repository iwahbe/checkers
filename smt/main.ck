# main.ck — the solver package's command line.
#
# `main parse` reads a query on standard input and writes it back.
# `main roundtrip DIR…` reads each query (`*.smt2`) in each DIR, writes it
# back, and checks that what it wrote is the same query. A query that can't be read gives
# `(error "line L column C: message")`, as Z3 reports one, and exit status 1.
# `main models DIR…` checks Z3's models in the corpus with `smt.model`, and
# `main model QUERY ANSWER` one query's assertions in one answer's model
# (`models.ck` says how).

module main

import std.system (System, ExitCode, Success, Failure)
import std.terminal (Term)
import std.files
import std.files (Fs, Entry)
import std.string
import std.bytes
import std.list
import smtlib (Shape, Group)
import term
import models

let USAGE = "usage: main parse < QUERY\n       main roundtrip DIR...\n       main models DIR...\n       main model QUERY ANSWER"

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    match args
        ["parse"]           -> parse_stdin sys.term
        "roundtrip" :: dirs -> roundtrip dirs sys.term sys.fs
        "models" :: dirs    -> if models.run dirs sys.term sys.fs then Success else Failure 1
        ["model", q, a]     -> model_one q a sys.term sys.fs
        _                   ->
            let _ = terminal.eprint_line USAGE sys.term
            Failure 2

fn model_one query ans io fs -> code : query~String, ans~String, io~Term, fs~Fs, code~ExitCode
    match (files.read query fs, files.read ans fs)
        (Ok src, Ok z3) ->
            let _ = terminal.write_bytes (models.one src z3) io
            Success
        (Err e, _)      ->
            let _ = terminal.eprint_line ("error: " ++ query ++ ": " ++ files.describe e) io
            Failure 2
        (_, Err e)      ->
            let _ = terminal.eprint_line ("error: " ++ ans ++ ": " ++ files.describe e) io
            Failure 2

fn error_line src e -> r : src~Bytes, e~smtlib.Error src, r~Bytes
    b"(error \"" ++ smtlib.describe src e ++ b"\")\n"

fn parse_stdin io -> code : io~Term, code~ExitCode
    match terminal.read_all io
        Err e  ->
            let _ = terminal.eprint_line ("error: standard input: " ++ files.describe e) io
            Failure 2
        Ok src ->
            match smtlib.parse src
                Ok q  ->
                    let _ = terminal.write_bytes (smtlib.render q) io
                    Success
                Err e ->
                    let _ = terminal.write_bytes (error_line src e) io
                    Failure 1

# How many queries were read, and how many came back the same.
record Tally
    read~Nat
    same~Nat

fn roundtrip dirs io fs -> code : dirs~List String, io~Term, fs~Fs, code~ExitCode
    match in_dirs dirs io fs (Tally 0 0)
        None   -> Failure 2
        Some t ->
            let summary = string.concat [string.display t.read [], " queries read, ", string.display t.same [], " round-trip, ",
                                         string.display (t.read - t.same) [], " don't"]
            let _ = terminal.print_line summary io
            if t.same == t.read then Success else Failure 1

# The queries of each of `dirs`, counted onto `t`; none if one can't be listed.
fn in_dirs dirs io fs t -> r : dirs~List String, io~Term, fs~Fs, t~Tally, t.same <= t.read,
                               r~Option (u~Tally, u.same <= u.read)
    match dirs
        []          -> Some t
        dir :: rest ->
            match files.list dir fs
                Err e ->
                    let _ = terminal.eprint_line ("error: " ++ dir ++ ": " ++ files.describe e) io
                    None
                Ok es -> in_dirs rest io fs (each dir es io fs t)

# Whether `name` is a query's file.
fn is_query name -> r : name~String, r~Bool
    let b = string.bytes name
    len b > 5 and bytes.matches_at b (len b - 5) b".smt2"

fn each dir es io fs t -> r : dir~String, es~List Entry, io~Term, fs~Fs, t~Tally, t.same <= t.read, r~Tally,
                              r.same <= r.read
    match es
        []        -> t
        e :: rest ->
            if e.dir or not (is_query e.name)
                each dir rest io fs t
            else
                let path = dir ++ "/" ++ e.name
                let ok = one path io fs
                each dir rest io fs (Tally (t.read + 1) (if ok then t.same + 1 else t.same))

# Whether the query at `path` reads, and writing it gives it back; if not,
# say why.
fn one path io fs -> ok : path~String, io~Term, fs~Fs, ok~Bool
    match files.read path fs
        Err e  -> report path (string.bytes (files.describe e)) io
        Ok src ->
            match smtlib.parse src
                Err e -> report path (smtlib.describe src e) io
                Ok q  ->
                    let out = smtlib.render q
                    match (smtlib.read src, smtlib.read out)
                        (Ok a, Ok b) ->
                            let sig = term.signature q.context
                            match first_difference sig (smtlib.shapes a) (smtlib.shapes b) 1
                                None           -> True
                                Some (n, x, y) ->
                                    let what = b"command " ++ smtlib.numeral n ++ b" differs\n  read:    " ++ shown x
                                               ++ b"\n  written: " ++ shown y
                                    report path what io
                        (_, Err e)   -> report path (b"what was written doesn't read: " ++ smtlib.describe out e) io
                        (Err e, _)   -> report path (smtlib.describe src e) io

fn shown s -> r : s~Option Shape, r~Bytes
    match s
        Some x -> smtlib.shape_text x
        None   -> b"(nothing)"

# The first command, counting from `n`, where `xs` and `ys` differ.
fn first_difference sig xs ys n -> r : sig~term.Sig, xs~List Shape, ys~List Shape, n~Nat,
                                       r~Option (Nat, Option Shape, Option Shape)
    match (xs, ys)
        ([], [])           -> None
        (x :: xr, y :: yr) -> if smtlib.same sig x y then first_difference sig xr yr (n + 1) else Some (n, Some x, Some y)
        (x :: _, [])       -> Some (n, Some x, None)
        ([], y :: _)       -> Some (n, None, Some y)

fn report path what io -> ok : path~String, what~Bytes, io~Term, ok~Bool
    let _ = terminal.write_bytes (string.bytes path ++ b": " ++ what ++ b"\n") io
    False
