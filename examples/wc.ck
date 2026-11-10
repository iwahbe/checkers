# wc.ck — count lines, words and bytes, like `wc`. First CLI target (M2).
#
#   wc               counts stdin
#   wc FILE...       counts each file; exits with Failure 1 if any can't be read
#
# Effects go through capabilities (SPEC §8). `fs` and `term` are authority
# capabilities: they can be used as often as needed and need no threading.

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

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { fs, term } = sys
    match args
        []    ->
            match terminal.read_all term
                Ok src ->
                    terminal.print_line (render (count src) "") term
                    Success
                Err e  ->
                    terminal.eprint_line ("wc: " ++ terminal.describe e) term
                    Failure 1
        paths ->
            report paths Success fs term

fn report paths status fs term -> code : paths~List String, status~ExitCode,
                                         fs~Fs, term~Term, code~ExitCode
    match paths
        []           -> status
        path :: rest ->
            match files.read path fs
                Ok src ->
                    terminal.print_line (render (count src) path) term
                    report rest status fs term
                Err e  ->
                    terminal.eprint_line ("wc: " ++ path ++ ": " ++ files.describe e) term
                    report rest (Failure 1) fs term

check count b"hello world\nbye\n" == Counts 2 3 16
check count b"" == Counts 0 0 0
check render (Counts 1 2 3) "f.txt" == "1 2 3 f.txt"
