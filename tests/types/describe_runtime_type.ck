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

# A field's type computed from a ghost field, which isn't kept.
record ByGhost
    is_text~ghost Bool
    v~(if is_text then String else Int)

fn ghosted r -> s : r~ByGhost, s~String
    debug r                                     # error E0293

# A field's type computed from a value the type is applied to: known when
# the program is compiled, or not.
record ByParam b : b~Bool
    v~(if b then String else Int)

fn known r -> s : r~ByParam True, s~String
    shown r

fn unknown b r -> s : b~Bool, r~ByParam b, s~String
    shown r                                     # error E0293

# Showing nothing of it is fine.
fn counted b x -> n : b~Bool, x~(if b then U8 else Int), n~Nat
    len [x]
