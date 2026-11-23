module parse_int

# Whole numbers read from the front of bytes, lists of bytes and strings,
# and how many tokens are left after each; and numbers written with
# `display` read back.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.array
import std.parse (Parsable, NumberError)
import std.string (debug, display)

fn shown r -> t : Seq s, r~Result (Int, s) NumberError, t~String
    match r
        Ok (n, rest) -> display n [] ++ ", " ++ debug (Seq.size rest) ++ " left"
        Err e        -> debug e

fn natural r -> t : Seq s, r~Result (Nat, s) NumberError, t~String
    match r
        Ok (n, rest) -> display n [] ++ ", " ++ debug (Seq.size rest) ++ " left"
        Err e        -> debug e

fn both b term -> r : b~Bytes, term~Term, r~Unit
    terminal.print_line (shown (Parsable.parse b Int Int)) term
    terminal.print_line (shown (Parsable.parse (array.to_list b) Int Int)) term
    terminal.print_line (natural (parse.natural b)) term

fn back n term -> r : n~Int, term~Term, r~Unit
    terminal.print_line (shown (Parsable.parse (display n [] ++ ")") Int Int)) term

export fn main args sys -> code
    let System { term } = sys
    both b"42" term
    both b"-42," term
    both b"007x" term
    both b"-0" term
    both b"0.5" term
    both b"+1" term
    both b"-" term
    both b"--1" term
    both b"x" term
    both b"" term
    terminal.print_line (shown (Parsable.parse "12345678901234567890123456789 apples" Int Int)) term
    terminal.print_line (shown (Parsable.parse "€1" Int Int)) term
    back 0 term
    back (-7) term
    back 170141183460469231731687303715884105728 term
    Success
