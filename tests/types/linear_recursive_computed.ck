module linear_recursive_computed

# A recursive type whose field's type is computed from its argument holds
# a resource only if one of its fields' types is one: `Chain 0` holds
# `Int`s.

import std.files (File)

fn pick n -> r : n~Nat, r~Type
    if n == 0 then Int else File

enum Chain n : n~Nat
    End
    Link x rest : x~pick n, rest~Chain n

fn plain c -> r : c~Chain 0, r~Unit
    let _ = c
    ()

fn files c -> r : c~Chain 1, r~Unit
    let _ = c
    ()
