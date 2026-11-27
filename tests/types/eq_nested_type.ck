module eq_nested_type

# A type whose fields hold it at other arguments (`Nest a` holds a
# `Nest (Option a)`) holds infinitely many types. `==` compares it when
# none of them holds a function.

enum Nest a : a~Type
    Flat
    Deeper x rest : x~a, rest~Nest (Option a)

fn same a b -> r : a~Nest Int, b~Nest Int, r~Bool
    a == b

fn of_functions a b -> r : a~Nest (Int -> Int), b~Nest (Int -> Int), r~Bool
    a == b

# The function is in `Grow (Int -> Int)`, which `Grow Int` holds.
enum Grow a : a~Type
    Stop
    Step x rest : x~a, rest~Grow (a -> a)

fn grown a b -> r : a~Grow Int, b~Grow Int, r~Bool
    a == b

# A field's type computed from the type's argument, which grows: whether
# one of them is a function can't be known.
fn pick n -> r : n~Nat, r~Type
    if n == 2 then Int -> Int else Int

enum Count n : n~Nat
    Done
    More x rest : x~pick n, rest~Count (n + 1)

fn counted a b -> r : a~Count 0, b~Count 0, r~Bool
    a == b
