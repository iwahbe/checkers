module match_refines_context

# In an arm of `match s`, where `s` is a variable, every variable whose type
# mentions `s` has that type with `s` replaced by the arm's pattern (D173).

import std.files (File)
import std.files

enum Shape
    One
    Many

fn values s a -> t : s~Shape, a~Type, t~Type
    match s
        One  -> a
        Many -> List a

fn count s x -> n : s~Shape, x~values s Int, n~Nat
    match s
        One  -> 1
        Many -> len x

fn first s x -> n : s~Shape, x~values s Int, n~Int
    match s
        One  -> x + 1
        Many ->
            match x
                []     -> 0
                y :: _ -> y

# A `let` whose type mentions `s` is refined too, and so is a function.
fn sum s x f -> n : s~Shape, x~values s Int, f~(values s Int -> Int), n~Int
    let y = x
    match s
        One  -> y + f y
        Many -> len y + f y

check count Many [1, 2, 3] == 3
check first One 5 == 6
check first Many [7, 8] == 7

fn same s -> t : s~Shape, t~Shape
    s

# Not refined: the matched value isn't a variable.
fn not_var s x -> n : s~Shape, x~values s Int, n~Int
    match same s
        One  -> x
        Many -> 0

# Not refined outside the arm.
fn outside s x -> n : s~Shape, x~values s Int, n~Int
    let k = match s
        One  -> 1
        Many -> 2
    x + k

# A type that is a resource in one arm only: there it must be used; in the
# other it holds none and may go unused.
fn handle s -> t : s~Shape, t~Type
    match s
        One  -> File
        Many -> Unit

fn finish s h -> r : s~Shape, h~handle s, r~Unit
    match s
        One  -> close h
        Many -> ()

fn forget s h -> r : s~Shape, h~handle s, r~Unit
    match s
        One  -> ()
        Many -> ()

# Close `f`, whatever closing gives.
fn close f : f~File
    let _ = files.close f
    ()
