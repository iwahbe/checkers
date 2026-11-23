module parse_combinators

# Std.parse's combinators: each alone on bytes, then a grammar for sums with
# brackets, whose bracketed rule refers to itself through `fix`.

import std.system (System, ExitCode)
import std.terminal
import std.parse (consumed, satisfy, at_end, map, both, or_else, optional, many, many1, sep_by1, chain_left, complete,
                  fix)
import std.string (debug)

# ── Pieces ──

fn digit xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    map (\c -> c - '0') (\ys -> satisfy (\c -> c >= '0' and c <= '9') () ys) xs

fn byte_of c xs -> r : c~Int, xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    satisfy (\k -> k == c) () xs

fn plus xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    byte_of '+' xs

fn comma xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    byte_of ',' xs

# A number: one or more digits.
fn number xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    map (\ds -> to_number ds 0) (\ys -> many1 digit ys) xs

fn to_number ds acc -> n : ds~List Int, acc~Int, n~Int
    match ds
        []        -> acc
        d :: rest -> to_number rest (acc * 10 + d)

# ── A grammar: sum := term ('+' term)*, term := number | '(' sum ')' ──

enum Expr
    Num n   : n~Int
    Add x y : x~Expr, y~Expr

fn sum xs -> r : xs~Bytes, r~Result (Expr, Bytes) Unit, consumed r xs
    fix (\zs self -> chain_left (\ys -> term self zs ys) plus Add zs) xs

# `self` is `sum`, callable on less than `top`.
fn term self top xs -> r : self~(ys~Bytes -> sr~Result (Expr, Bytes) Unit, len ys < len top, consumed sr ys),
                           top~ghost Bytes, xs~Bytes, len xs <= len top, r~Result (Expr, Bytes) Unit, consumed r xs
    or_else (\ys -> map Num number ys) (\ys -> bracketed self top ys) xs

fn bracketed self top xs -> r : self~(ys~Bytes -> sr~Result (Expr, Bytes) Unit, len ys < len top, consumed sr ys),
                                top~ghost Bytes, xs~Bytes, len xs <= len top,
                                r~Result (Expr, Bytes) Unit, consumed r xs
    match byte_of '(' xs
        Err e         -> Err e
        Ok (_, after) ->
            match self after
                Err e           -> Err e
                Ok (inner, mid) ->
                    match byte_of ')' mid
                        Err e        -> Err e
                        Ok (_, rest) -> Ok (inner, rest)

fn shown e -> s : e~Expr, s~String
    match e
        Num n   -> debug n
        Add x y -> "(" ++ shown x ++ " + " ++ shown y ++ ")"

fn tree r -> s : r~Result (Expr, Bytes) Unit, s~String
    match r
        Ok (e, rest) -> shown e ++ ", " ++ debug (len rest) ++ " left"
        Err _        -> "no expression"

export fn main args sys -> code
    let System { term } = sys
    terminal.print_line (debug (digit b"7x")) term
    terminal.print_line (debug (number b"123x")) term
    terminal.print_line (debug (optional plus b"+1")) term
    terminal.print_line (debug (optional plus b"1")) term
    terminal.print_line (debug (many digit b"12x")) term
    terminal.print_line (debug (many digit b"x")) term
    terminal.print_line (debug (many1 digit b"x")) term
    terminal.print_line (debug (both digit plus b"1+")) term
    terminal.print_line (debug (or_else plus digit b"5")) term
    terminal.print_line (debug (sep_by1 number comma b"1,22,333;")) term
    terminal.print_line (debug (chain_left number plus (\a b -> a + b) b"1+2+3")) term
    terminal.print_line (debug (complete number () b"42")) term
    terminal.print_line (debug (complete number () b"42x")) term
    terminal.print_line (debug (at_end () b"")) term
    terminal.print_line (tree (sum b"1+(2+3)+4")) term
    terminal.print_line (tree (sum b"(1+2")) term
    Success
