module sealed_lib

# A library for `sealed_use.ck` (SPEC §6, D54).

export fn double x -> y : x~Int, y~Int, y == x + x
    x + x

export fn triple x -> y : x~Int, y~Int
    x + x + x

export lemma triple_is x : x~Int
    ensures triple x == 3 * x

export transparent fn quad x -> y : x~Int, y~Int
    4 * x

export fn two -> n : n~Nat
    2

export transparent fn three -> n : n~Nat
    3
