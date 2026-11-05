# wc.ck — count lines, words and bytes, like `wc`. First CLI target (M2).
#
#   wc               counts stdin
#   wc FILE...       counts each file; exits with Failure 1 if any can't be read
#
# Effects are linear capabilities (SPEC §8): `main` receives `sys` and keeps
# only `fs` and `term`; the other capabilities are dropped.

module wc

import system (System, ExitCode)
import terminal (Term)
import files (Fs)

record Counts
    lines~Nat
    words~Nat
    bytes~Nat

# Pure, and its postcondition is checked: every byte is counted exactly once.
fn count src -> c : src~Bytes, c~Counts, c.bytes == len src
    count_from src 0 False (Counts 0 0 0)

fn count_from src i in_word acc -> c : src~Bytes, i~Nat, i <= len src, in_word~Bool, acc~Counts,
                                       c~Counts, c.bytes == acc.bytes + (len src - i)
    decreasing len src - i
    if i == len src
        acc
    else
        let b = src[i]
        let space = b == ' ' or b == '\n' or b == '\t' or b == '\r'
        let lines = if b == '\n' then acc.lines + 1 else acc.lines
        let words = if not space and not in_word then acc.words + 1 else acc.words
        count_from src (i + 1) (not space) (Counts lines words (acc.bytes + 1))

fn render c name -> s : c~Counts, name~String, s~String
    format c.lines ++ " " ++ format c.words ++ " " ++ format c.bytes ++ " " ++ name

export fn main args sys -> code : args~List String, sys~own System, code~ExitCode
    let System { fs, term } = sys
    match args
        [] ->
            input <- terminal.read_all term
            match input
                Ok src ->
                    _ <- terminal.print_line (render (count src) "") term
                    Success
                Err e ->
                    _ <- terminal.eprint_line ("wc: " ++ terminal.describe e) term
                    Failure 1
        paths ->
            report paths Success fs term

# Both capabilities are threaded through the recursion and used exactly once
# on every path; when the list is empty they are dropped.
fn report paths status fs term -> code : paths~List String, status~ExitCode,
                                         fs~own Fs, term~own Term, code~ExitCode
    match paths
        [] -> status
        path :: rest ->
            contents <- files.read path fs
            match contents
                Ok src ->
                    _ <- terminal.print_line (render (count src) path) term
                    report rest status fs term
                Err e ->
                    _ <- terminal.eprint_line ("wc: " ++ path ++ ": " ++ files.describe e) term
                    report rest (Failure 1) fs term

check count b"hello world\nbye\n" == Counts 2 3 16
check count b"" == Counts 0 0 0
check render (Counts 1 2 3) "f.txt" == "1 2 3 f.txt"
