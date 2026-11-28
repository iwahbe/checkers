module lambda_param_use

# A closure's parameter that must be used once is reported where the
# closure binds it, even when two closures use the same name (#672 d).

import std.files (File)

enum Shape
    One
    Many

# A `File` for `One`: a value of `handle s` may be a resource.
fn handle s -> t : s~Shape, t~Type
    match s
        One  -> File
        Many -> Unit

fn pair s -> r : s~Shape, r~((handle s -> handle s), (handle s -> Unit))
    (\x -> x, \x -> ())

fn copy x -> r : x~a, r~(a, a)
    (x, x)

fn twice s -> k : s~Shape, k~(handle s -> (handle s, handle s))
    \x -> copy x
