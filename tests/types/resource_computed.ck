# A field whose type is computed from the record's parameters (D112): the
# record holds a resource for some arguments and not others. Where the
# arguments are known the field types are computed; where they aren't, the
# value counts as a resource, since it may hold one.
module resource_computed

import std.files (File)

enum Stream
    Inherit
    Pipe

fn pipe_end s -> t : s~Stream, t~Type
    match s
        Pipe -> File
        _    -> Unit

record Ends a b : a~Stream, b~Stream
    first~pipe_end a
    second~pipe_end b

# Fine: nothing piped, nothing to close.
fn neither e -> r : e~Ends Inherit Inherit, r~Unit
    ()

# E0401: `e` holds a file.
fn dropped e -> r : e~Ends Pipe Inherit, r~Unit
    ()

# Fine: the file is closed, the other end is `()`.
fn closed e -> r : e~Ends Pipe Inherit, r~Unit
    let Ends { first, second } = e
    files.close first

# E0401, showing the computed type: `first` is a `File`.
fn forgotten e -> r : e~Ends Pipe Inherit, r~Unit
    let Ends { first, second } = e
    ()

# E0201: the second end is `Unit`, not a `File`.
fn wrong e -> r : e~Ends Inherit Pipe, r~Unit
    let Ends { first, second } = e
    files.close first

# E0401: which ends are files isn't known here, so `e` may hold one.
fn generic a b e -> r : a~Stream, b~Stream, e~Ends a b, r~Unit
    ()

# Fine: passed on whole.
fn passed a b e -> r : a~Stream, b~Stream, e~Ends a b, r~Ends a b
    e
