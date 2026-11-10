# wc.ck — count lines, words and bytes, like `wc`. First CLI target (M2).
#
#   wc               counts stdin
#   wc FILE...       counts each file; exits with Failure 1 if any can't be read
#
# Effects go through capabilities (SPEC §8). `fs` and `term` are authority
# capabilities: they can be used as often as needed and need no threading.
# Input is read a block at a time, so any size can be counted (D112).

module wc

import std.system (System, ExitCode)
import std.terminal (Term)
import std.files (Fs, File, IoError)

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
        let space = is_space b
        let lines = if b == '\n' then acc.lines + 1 else acc.lines
        let words = if not space and not in_word then acc.words + 1 else acc.words
        count_from src (i + 1) (not space) (Counts lines words (acc.bytes + 1))

fn is_space b : b~U8
    b == ' ' or b == '\n' or b == '\t' or b == '\r'

# Whether the input so far ends inside a word, after `src`.
fn ends_in_word src in_word : src~Bytes, in_word~Bool
    if len src == 0 then in_word else not (is_space src[len src - 1])

let BLOCK = 65536

# Count the rest of `f`, a block at a time, from the counts so far.
partial fn count_file f in_word acc -> r : f~File, in_word~Bool, acc~Counts, r~Result Counts IoError
    block <- files.read_some BLOCK f
    match block
        Ok b  ->
            if len b == 0
                files.close f
                Ok acc
            else
                count_file f (ends_in_word b in_word) (count_from b 0 in_word acc)
        Err e ->
            files.close f
            Err e

fn render c name -> s : c~Counts, name~String, s~String
    format c.lines ++ " " ++ format c.words ++ " " ++ format c.bytes ++ " " ++ name

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { fs, term } = sys
    match args
        []    ->
            match count_file (terminal.stdin term) False (Counts 0 0 0)
                Ok c  ->
                    terminal.print_line (render c "") term
                    Success
                Err e ->
                    terminal.eprint_line ("wc: " ++ terminal.describe e) term
                    Failure 1
        paths ->
            report paths Success fs term

partial fn report paths status fs term -> code : paths~List String, status~ExitCode,
                                                 fs~Fs, term~Term, code~ExitCode
    match paths
        []           -> status
        path :: rest ->
            match try_count path fs
                Ok c  ->
                    terminal.print_line (render c path) term
                    report rest status fs term
                Err e ->
                    terminal.eprint_line ("wc: " ++ path ++ ": " ++ files.describe e) term
                    report rest (Failure 1) fs term

partial fn try_count path fs -> r : path~String, fs~Fs, r~Result Counts IoError
    match files.open path fs
        Ok f  -> count_file f False (Counts 0 0 0)
        Err e -> Err e

check count b"hello world\nbye\n" == Counts 2 3 16
check count b"" == Counts 0 0 0
check render (Counts 1 2 3) "f.txt" == "1 2 3 f.txt"
check ends_in_word b"ab" False
check not (ends_in_word b"ab " True)
check ends_in_word b"" True
