# json.ck — reads JSON on standard input and prints it in compact form, or
# where it is malformed. The parser, and its proofs, are `std.json`.

module json

import std.system (System, ExitCode)
import std.terminal
import std.string
import std.char
import std.json (Error, ErrorKind)

# Line and column (from 1) of byte `pos` in `src`.
fn line_col src pos -> r : src~Bytes, pos~Nat, pos <= len src, r~(Nat, Nat)
    lines src pos 0 1 1

fn lines src pos i line col -> r : src~Bytes, pos~Nat, pos <= len src, i~Nat, i <= pos,
                                   line~Nat, col~Nat, r~(Nat, Nat)
    decreasing pos - i
    if i == pos
        (line, col)
    else if src[i] == '\n'
        lines src pos (i + 1) (line + 1) 1
    else
        lines src pos (i + 1) line (col + 1)

# A byte as it reads: `']'`, or its number if it isn't printable ASCII.
fn shown b -> s : b~U8, s~String
    if b >= 0x20 and b < 0x7F then "'" ++ string.from_char (char.from_ascii b) ++ "'" else "byte " ++ format b

fn explain k -> s : k~ErrorKind, s~String
    match k
        UnexpectedEnd    -> "the input ends too soon"
        UnexpectedByte b -> "unexpected " ++ shown b
        BadEscape        -> "a bad escape sequence"
        BadUtf8          -> "bytes that are not UTF-8"
        ControlInString  -> "a control character in a string"
        DuplicateKey k   -> "the key \"" ++ k ++ "\" twice"
        TooDeep          -> "nesting deeper than " ++ format json.MAX_DEPTH
        TrailingInput    -> "more after the value"

fn describe src e -> s : src~Bytes, e~Error src, s~String
    let (line, col) = line_col src e.pos
    "<stdin>:" ++ format line ++ ":" ++ format col ++ ": " ++ explain e.kind

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    match terminal.read_all term
        Err e  ->
            terminal.eprint_line ("json: " ++ terminal.describe e) term
            Failure 1
        Ok src ->
            match json.parse src
                Ok v  ->
                    terminal.print_line (json.render v) term
                    Success
                Err e ->
                    terminal.eprint_line (describe src e) term
                    Failure 1

check line_col b"[1,\n 2,]" 7 == (2, 4)
check explain (DuplicateKey "a") == "the key \"a\" twice"
check shown ']' == "']'"
check shown 0x0A == "byte 10"
