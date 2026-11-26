module type_eq_gadt_eval

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

enum Expr t : t~Type
    Lit n    : n~Int, t == Int
    Truth b  : b~Bool, t == Bool
    Add x y  : x~Expr Int, y~Expr Int, t == Int
    IsZero x : x~Expr Int, t == Bool
    If c x y : c~Expr Bool, x~Expr t, y~Expr t

fn eval e -> r : e~Expr t, r~t
    match e
        Lit n    -> n
        Truth b  -> b
        Add x y  -> eval x + eval y
        IsZero x -> eval x == 0
        If c x y -> if eval c then eval x else eval y

export fn main args sys -> code
    let System { term } = sys
    terminal.print_line (debug (eval (Add (Lit 2) (Lit 3)))) term
    terminal.print_line (debug (eval (IsZero (Add (Lit 1) (Lit (-1)))))) term
    terminal.print_line (debug (eval (If (Truth False) (Lit 1) (Lit 2)))) term
    Success
