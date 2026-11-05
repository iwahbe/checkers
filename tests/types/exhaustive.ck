module exhaustive

enum Color
    Red
    Green
    Blue

fn missing c -> n : c~Color, n~Nat
    match c
        Red   -> 1
        Green -> 2

fn nested o -> n : o~Option Color, n~Nat
    match o
        None     -> 0
        Some Red -> 1

fn literals n -> s : n~Nat, s~String
    match n
        0 -> "zero"
        1 -> "one"

fn guarded n -> s : n~Nat, s~String
    match n
        _ if n > 5 -> "big"

fn wrong_type c -> n : c~Color, n~Nat
    match c
        Some _ -> 1
        _      -> 0

fn arity o -> n : o~Option Nat, n~Nat
    match o
        Some a b -> a
        None     -> 0

fn unknown_ctor c -> n : c~Color, n~Nat
    match c
        Purple -> 1
        _      -> 0

fn complete c -> n : c~Color, n~Nat
    match c
        Red   -> 1
        Green -> 2
        Blue  -> 3
