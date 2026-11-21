module describe_runtime_type

# A type whose values are shown must be known when the program is
# compiled: a type that depends on a value has no descriptor to pass.

import std.string (debug)

fn shown x -> s : x~a, s~String
    debug x

fn direct b x -> s : b~Bool, x~(if b then U8 else Int), s~String
    debug x                                     # error E0293

fn through b x -> s : b~Bool, x~(if b then U8 else Int), s~String
    shown x                                     # error E0293

fn inside b x -> s : b~Bool, x~(if b then U8 else Int), s~String
    shown [x]                                   # error E0293

# Showing nothing of it is fine.
fn counted b x -> n : b~Bool, x~(if b then U8 else Int), n~Nat
    len [x]
