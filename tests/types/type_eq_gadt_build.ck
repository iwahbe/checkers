module type_eq_gadt_build

# A constructor's type equation fixes the type it builds: an ill-typed
# expression can't be built.

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

fn not_an_int -> e : e~Expr Int
    IsZero (Lit 0)

fn zero_of_bool -> e : e~Expr Bool
    IsZero (Truth True)
