module type_eq_gadt_cases

# A case whose constructor builds another type than the value's can't
# occur: it needn't be covered, and its arm never runs.

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

fn int_value e -> n : e~Expr Int, n~Int
    match e
        Lit n    -> n
        Add x y  -> int_value x + int_value y
        If c x y -> if eval c then int_value x else int_value y

fn with_dead_arm e -> n : e~Expr Int, n~Int
    match e
        Lit n   -> n
        Truth _ -> 0
        _       -> 0

fn missing_if e -> n : e~Expr Int, n~Int
    match e
        Lit n   -> n
        Add x y -> missing_if x + missing_if y
