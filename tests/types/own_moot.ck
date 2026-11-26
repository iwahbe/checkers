module own_moot

# `own` on a function type's parameter (D172 b): written as `(v~own a -> b)`,
# and implied when the parameter's type may be a resource. Once that type is
# known to hold none, `own` means nothing.

import std.files (File)
import std.files

enum Shape
    One
    Many

# A `File` for `One`: a value of `handle s` may be a resource.
fn handle s -> t : s~Shape, t~Type
    match s
        One  -> File
        Many -> Unit

fn twice f -> r : f~(Unit -> Unit), r~Unit
    f (f ())

# The type of `k` takes its parameter `own`, since `handle s` may be a
# `File`; at `Many` it is `Unit -> Unit`.
fn each s -> k : s~Shape, k~(handle s -> Unit)
    match s
        One  -> \f -> close f
        Many -> \u -> u

check twice (each Many) == ()

fn apply x f -> r : x~own a, f~own (v~own a -> b), r~b
    f x

# At `Nat`, the closure's parameter may be used twice.
check apply 3 (\n -> n * n) == 9

fn close_both f g -> r : f~File, g~File, r~Unit
    apply f $ \h ->
        close h
        close g

fn close_twice f -> r : f~File, r~Unit
    apply f $ \h ->
        close h
        close h

fn on_int f -> r : f~(v~own Int -> Int), r~Int
    f 1

fn on_file f -> r : f~(v~own File -> Unit), r~Unit
    ()

# Close `f`, whatever closing gives.
fn close f : f~File
    let _ = files.close f
    ()
